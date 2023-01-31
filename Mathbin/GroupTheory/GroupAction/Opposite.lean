/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module group_theory.group_action.opposite
! leanprover-community/mathlib commit bcfa726826abd57587355b4b5b7e78ad6527b7e4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Opposite
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the actions on the opposite type `has_smul R Mᵐᵒᵖ`, and actions by the opposite
type, `has_smul Rᵐᵒᵖ M`.

Note that `mul_opposite.has_smul` is provided in an earlier file as it is needed to provide the
`add_monoid.nsmul` and `add_comm_group.gsmul` fields.
-/


variable (α : Type _)

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/


namespace MulOpposite

@[to_additive]
instance (R : Type _) [Monoid R] [MulAction R α] : MulAction R αᵐᵒᵖ :=
  {
    MulOpposite.hasSmul α
      R with
    one_smul := fun x => unop_injective <| one_smul R (unop x)
    mul_smul := fun r₁ r₂ x => unop_injective <| mul_smul r₁ r₂ (unop x) }

instance (R : Type _) [Monoid R] [AddMonoid α] [DistribMulAction R α] : DistribMulAction R αᵐᵒᵖ :=
  {
    MulOpposite.mulAction α
      R with
    smul_add := fun r x₁ x₂ => unop_injective <| smul_add r (unop x₁) (unop x₂)
    smul_zero := fun r => unop_injective <| smul_zero r }

instance (R : Type _) [Monoid R] [Monoid α] [MulDistribMulAction R α] :
    MulDistribMulAction R αᵐᵒᵖ :=
  {
    MulOpposite.mulAction α
      R with
    smul_mul := fun r x₁ x₂ => unop_injective <| smul_mul' r (unop x₂) (unop x₁)
    smul_one := fun r => unop_injective <| smul_one r }

@[to_additive]
instance {M N} [SMul M N] [SMul M α] [SMul N α] [IsScalarTower M N α] : IsScalarTower M N αᵐᵒᵖ :=
  ⟨fun x y z => unop_injective <| smul_assoc _ _ _⟩

@[to_additive]
instance {M N} [SMul M α] [SMul N α] [SMulCommClass M N α] : SMulCommClass M N αᵐᵒᵖ :=
  ⟨fun x y z => unop_injective <| smul_comm _ _ _⟩

@[to_additive]
instance (R : Type _) [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] : IsCentralScalar R αᵐᵒᵖ :=
  ⟨fun r m => unop_injective <| op_smul_eq_smul _ _⟩

#print MulOpposite.op_smul_eq_op_smul_op /-
theorem op_smul_eq_op_smul_op {R : Type _} [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α] (r : R)
    (a : α) : op (r • a) = op r • op a :=
  (op_smul_eq_smul r (op a)).symm
#align mul_opposite.op_smul_eq_op_smul_op MulOpposite.op_smul_eq_op_smul_op
-/

#print MulOpposite.unop_smul_eq_unop_smul_unop /-
theorem unop_smul_eq_unop_smul_unop {R : Type _} [SMul R α] [SMul Rᵐᵒᵖ α] [IsCentralScalar R α]
    (r : Rᵐᵒᵖ) (a : αᵐᵒᵖ) : unop (r • a) = unop r • unop a :=
  (unop_smul_eq_smul r (unop a)).symm
#align mul_opposite.unop_smul_eq_unop_smul_unop MulOpposite.unop_smul_eq_unop_smul_unop
-/

end MulOpposite

/-! ### Actions _by_ the opposite type (right actions)

In `has_mul.to_has_smul` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `mul_opposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/


open MulOpposite

#print Mul.toHasOppositeSMul /-
/-- Like `has_mul.to_has_smul`, but multiplies on the right.

See also `monoid.to_opposite_mul_action` and `monoid_with_zero.to_opposite_mul_action_with_zero`. -/
@[to_additive
      "Like `has_add.to_has_vadd`, but adds on the right.\n\nSee also `add_monoid.to_opposite_add_action`."]
instance Mul.toHasOppositeSMul [Mul α] : SMul αᵐᵒᵖ α :=
  ⟨fun c x => x * c.unop⟩
#align has_mul.to_has_opposite_smul Mul.toHasOppositeSMul
#align has_add.to_has_opposite_vadd Add.toHasOppositeVAdd
-/

#print op_smul_eq_mul /-
@[to_additive]
theorem op_smul_eq_mul [Mul α] {a a' : α} : op a • a' = a' * a :=
  rfl
#align op_smul_eq_mul op_smul_eq_mul
#align op_vadd_eq_add op_vadd_eq_add
-/

#print MulOpposite.smul_eq_mul_unop /-
@[simp, to_additive]
theorem MulOpposite.smul_eq_mul_unop [Mul α] {a : αᵐᵒᵖ} {a' : α} : a • a' = a' * a.unop :=
  rfl
#align mul_opposite.smul_eq_mul_unop MulOpposite.smul_eq_mul_unop
#align add_opposite.vadd_eq_add_unop AddOpposite.vadd_eq_add_unop
-/

/- warning: mul_action.opposite_regular.is_pretransitive -> MulAction.OppositeRegular.isPretransitive is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], MulAction.IsPretransitive.{u1, u1} (MulOpposite.{u1} G) G (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toHasMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : Group.{u1} G], MulAction.IsPretransitive.{u1, u1} (MulOpposite.{u1} G) G (Mul.toHasOppositeSMul.{u1} G (MulOneClass.toMul.{u1} G (Monoid.toMulOneClass.{u1} G (DivInvMonoid.toMonoid.{u1} G (Group.toDivInvMonoid.{u1} G _inst_1)))))
Case conversion may be inaccurate. Consider using '#align mul_action.opposite_regular.is_pretransitive MulAction.OppositeRegular.isPretransitiveₓ'. -/
/-- The right regular action of a group on itself is transitive. -/
@[to_additive "The right regular action of an additive group on itself is transitive."]
instance MulAction.OppositeRegular.isPretransitive {G : Type _} [Group G] :
    MulAction.IsPretransitive Gᵐᵒᵖ G :=
  ⟨fun x y => ⟨op (x⁻¹ * y), mul_inv_cancel_left _ _⟩⟩
#align mul_action.opposite_regular.is_pretransitive MulAction.OppositeRegular.isPretransitive
#align add_action.opposite_regular.is_pretransitive AddAction.OppositeRegular.isPretransitive

/- warning: semigroup.opposite_smul_comm_class -> Semigroup.opposite_smulCommClass is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Semigroup.{u1} α], SMulCommClass.{u1, u1, u1} (MulOpposite.{u1} α) α α (Mul.toHasOppositeSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Semigroup.{u1} α], SMulCommClass.{u1, u1, u1} (MulOpposite.{u1} α) α α (Mul.toHasOppositeSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align semigroup.opposite_smul_comm_class Semigroup.opposite_smulCommClassₓ'. -/
@[to_additive]
instance Semigroup.opposite_smulCommClass [Semigroup α] : SMulCommClass αᵐᵒᵖ α α
    where smul_comm x y z := mul_assoc _ _ _
#align semigroup.opposite_smul_comm_class Semigroup.opposite_smulCommClass
#align add_semigroup.opposite_vadd_comm_class AddSemigroup.opposite_vaddCommClass

/- warning: semigroup.opposite_smul_comm_class' -> Semigroup.opposite_smulCommClass' is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Semigroup.{u1} α], SMulCommClass.{u1, u1, u1} α (MulOpposite.{u1} α) α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)) (Mul.toHasOppositeSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Semigroup.{u1} α], SMulCommClass.{u1, u1, u1} α (MulOpposite.{u1} α) α (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)) (Mul.toHasOppositeSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align semigroup.opposite_smul_comm_class' Semigroup.opposite_smulCommClass'ₓ'. -/
@[to_additive]
instance Semigroup.opposite_smulCommClass' [Semigroup α] : SMulCommClass α αᵐᵒᵖ α :=
  SMulCommClass.symm _ _ _
#align semigroup.opposite_smul_comm_class' Semigroup.opposite_smulCommClass'
#align add_semigroup.opposite_vadd_comm_class' AddSemigroup.opposite_vaddCommClass'

/- warning: comm_semigroup.is_central_scalar -> CommSemigroup.isCentralScalar is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CommSemigroup.{u1} α], IsCentralScalar.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) (Mul.toHasOppositeSMul.{u1} α (Semigroup.toHasMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CommSemigroup.{u1} α], IsCentralScalar.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1))) (Mul.toHasOppositeSMul.{u1} α (Semigroup.toMul.{u1} α (CommSemigroup.toSemigroup.{u1} α _inst_1)))
Case conversion may be inaccurate. Consider using '#align comm_semigroup.is_central_scalar CommSemigroup.isCentralScalarₓ'. -/
instance CommSemigroup.isCentralScalar [CommSemigroup α] : IsCentralScalar α α :=
  ⟨fun r m => mul_comm _ _⟩
#align comm_semigroup.is_central_scalar CommSemigroup.isCentralScalar

/- warning: monoid.to_opposite_mul_action -> Monoid.toOppositeMulAction is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulAction.{u1, u1} (MulOpposite.{u1} α) α (MulOpposite.monoid.{u1} α _inst_1)
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Monoid.{u1} α], MulAction.{u1, u1} (MulOpposite.{u1} α) α (MulOpposite.instMonoidMulOpposite.{u1} α _inst_1)
Case conversion may be inaccurate. Consider using '#align monoid.to_opposite_mul_action Monoid.toOppositeMulActionₓ'. -/
/-- Like `monoid.to_mul_action`, but multiplies on the right. -/
@[to_additive "Like `add_monoid.to_add_action`, but adds on the right."]
instance Monoid.toOppositeMulAction [Monoid α] : MulAction αᵐᵒᵖ α
    where
  smul := (· • ·)
  one_smul := mul_one
  mul_smul x y r := (mul_assoc _ _ _).symm
#align monoid.to_opposite_mul_action Monoid.toOppositeMulAction
#align add_monoid.to_opposite_add_action AddMonoid.toOppositeAddAction

#print IsScalarTower.opposite_mid /-
@[to_additive]
instance IsScalarTower.opposite_mid {M N} [Mul N] [SMul M N] [SMulCommClass M N N] :
    IsScalarTower M Nᵐᵒᵖ N :=
  ⟨fun x y z => mul_smul_comm _ _ _⟩
#align is_scalar_tower.opposite_mid IsScalarTower.opposite_mid
#align vadd_assoc_class.opposite_mid VAddAssocClass.opposite_mid
-/

#print SMulCommClass.opposite_mid /-
@[to_additive]
instance SMulCommClass.opposite_mid {M N} [Mul N] [SMul M N] [IsScalarTower M N N] :
    SMulCommClass M Nᵐᵒᵖ N :=
  ⟨fun x y z => by
    induction y using MulOpposite.rec'
    simp [smul_mul_assoc]⟩
#align smul_comm_class.opposite_mid SMulCommClass.opposite_mid
#align vadd_comm_class.opposite_mid VAddCommClass.opposite_mid
-/

-- The above instance does not create an unwanted diamond, the two paths to
-- `mul_action αᵐᵒᵖ αᵐᵒᵖ` are defeq.
example [Monoid α] : Monoid.toMulAction αᵐᵒᵖ = MulOpposite.mulAction α αᵐᵒᵖ :=
  rfl

/- warning: left_cancel_monoid.to_has_faithful_opposite_scalar -> LeftCancelMonoid.toFaithfulSMul_opposite is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : LeftCancelMonoid.{u1} α], FaithfulSMul.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (LeftCancelMonoid.toMonoid.{u1} α _inst_1))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : LeftCancelMonoid.{u1} α], FaithfulSMul.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (LeftCancelMonoid.toMonoid.{u1} α _inst_1))))
Case conversion may be inaccurate. Consider using '#align left_cancel_monoid.to_has_faithful_opposite_scalar LeftCancelMonoid.toFaithfulSMul_oppositeₓ'. -/
/-- `monoid.to_opposite_mul_action` is faithful on cancellative monoids. -/
@[to_additive "`add_monoid.to_opposite_add_action` is faithful on cancellative monoids."]
instance LeftCancelMonoid.toFaithfulSMul_opposite [LeftCancelMonoid α] : FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun x y h => unop_injective <| mul_left_cancel (h 1)⟩
#align left_cancel_monoid.to_has_faithful_opposite_scalar LeftCancelMonoid.toFaithfulSMul_opposite
#align add_left_cancel_monoid.to_has_faithful_opposite_scalar AddLeftCancelMonoid.toFaithfulVAdd_opposite

/- warning: cancel_monoid_with_zero.to_has_faithful_opposite_scalar -> CancelMonoidWithZero.toFaithfulSMul_opposite is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : CancelMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α], FaithfulSMul.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulZeroClass.toHasMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : CancelMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α], FaithfulSMul.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulZeroClass.toMul.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CancelMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align cancel_monoid_with_zero.to_has_faithful_opposite_scalar CancelMonoidWithZero.toFaithfulSMul_oppositeₓ'. -/
/-- `monoid.to_opposite_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.toFaithfulSMul_opposite [CancelMonoidWithZero α] [Nontrivial α] :
    FaithfulSMul αᵐᵒᵖ α :=
  ⟨fun x y h => unop_injective <| mul_left_cancel₀ one_ne_zero (h 1)⟩
#align cancel_monoid_with_zero.to_has_faithful_opposite_scalar CancelMonoidWithZero.toFaithfulSMul_opposite

