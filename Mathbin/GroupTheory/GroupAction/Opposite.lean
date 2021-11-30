import Mathbin.Algebra.Group.Opposite 
import Mathbin.GroupTheory.GroupAction.Defs

/-!
# Scalar actions on and by `Mᵐᵒᵖ`

This file defines the actions on the opposite type `has_scalar R Mᵐᵒᵖ`, and actions by the opposite
type, `has_scalar Rᵐᵒᵖ M`.

Note that `mul_opposite.has_scalar` is provided in an earlier file as it is needed to provide the
`add_monoid.nsmul` and `add_comm_group.gsmul` fields.
-/


variable (α : Type _)

/-! ### Actions _on_ the opposite type

Actions on the opposite type just act on the underlying type.
-/


namespace MulOpposite

instance (R : Type _) [Monoidₓ R] [MulAction R α] : MulAction R («expr ᵐᵒᵖ» α) :=
  { MulOpposite.hasScalar α R with one_smul := fun x => unop_injective$ one_smul R (unop x),
    mul_smul := fun r₁ r₂ x => unop_injective$ mul_smul r₁ r₂ (unop x) }

instance (R : Type _) [Monoidₓ R] [AddMonoidₓ α] [DistribMulAction R α] : DistribMulAction R («expr ᵐᵒᵖ» α) :=
  { MulOpposite.mulAction α R with smul_add := fun r x₁ x₂ => unop_injective$ smul_add r (unop x₁) (unop x₂),
    smul_zero := fun r => unop_injective$ smul_zero r }

instance (R : Type _) [Monoidₓ R] [Monoidₓ α] [MulDistribMulAction R α] : MulDistribMulAction R («expr ᵐᵒᵖ» α) :=
  { MulOpposite.mulAction α R with smul_mul := fun r x₁ x₂ => unop_injective$ smul_mul' r (unop x₂) (unop x₁),
    smul_one := fun r => unop_injective$ smul_one r }

instance {M N} [HasScalar M N] [HasScalar M α] [HasScalar N α] [IsScalarTower M N α] :
  IsScalarTower M N («expr ᵐᵒᵖ» α) :=
  ⟨fun x y z => unop_injective$ smul_assoc _ _ _⟩

instance {M N} [HasScalar M α] [HasScalar N α] [SmulCommClass M N α] : SmulCommClass M N («expr ᵐᵒᵖ» α) :=
  ⟨fun x y z => unop_injective$ smul_comm _ _ _⟩

end MulOpposite

/-! ### Actions _by_ the opposite type (right actions)

In `has_mul.to_has_scalar` in another file, we define the left action `a₁ • a₂ = a₁ * a₂`. For the
multiplicative opposite, we define `mul_opposite.op a₁ • a₂ = a₂ * a₁`, with the multiplication
reversed.
-/


open MulOpposite

/-- Like `has_mul.to_has_scalar`, but multiplies on the right.

See also `monoid.to_opposite_mul_action` and `monoid_with_zero.to_opposite_mul_action_with_zero`. -/
instance Mul.toHasOppositeScalar [Mul α] : HasScalar («expr ᵐᵒᵖ» α) α :=
  { smul := fun c x => x*c.unop }

@[simp]
theorem op_smul_eq_mul [Mul α] {a a' : α} : op a • a' = a'*a :=
  rfl

/-- The right regular action of a group on itself is transitive. -/
instance MulAction.OppositeRegular.is_pretransitive {G : Type _} [Groupₓ G] :
  MulAction.IsPretransitive («expr ᵐᵒᵖ» G) G :=
  ⟨fun x y => ⟨op (x⁻¹*y), mul_inv_cancel_left _ _⟩⟩

instance Semigroupₓ.opposite_smul_comm_class [Semigroupₓ α] : SmulCommClass («expr ᵐᵒᵖ» α) α α :=
  { smul_comm := fun x y z => mul_assocₓ _ _ _ }

instance Semigroupₓ.opposite_smul_comm_class' [Semigroupₓ α] : SmulCommClass α («expr ᵐᵒᵖ» α) α :=
  { smul_comm := fun x y z => (mul_assocₓ _ _ _).symm }

/-- Like `monoid.to_mul_action`, but multiplies on the right. -/
instance Monoidₓ.toOppositeMulAction [Monoidₓ α] : MulAction («expr ᵐᵒᵖ» α) α :=
  { smul := · • ·, one_smul := mul_oneₓ, mul_smul := fun x y r => (mul_assocₓ _ _ _).symm }

instance IsScalarTower.opposite_mid {M N} [Monoidₓ N] [HasScalar M N] [SmulCommClass M N N] :
  IsScalarTower M («expr ᵐᵒᵖ» N) N :=
  ⟨fun x y z => mul_smul_comm _ _ _⟩

instance SmulCommClass.opposite_mid {M N} [Monoidₓ N] [HasScalar M N] [IsScalarTower M N N] :
  SmulCommClass M («expr ᵐᵒᵖ» N) N :=
  ⟨fun x y z =>
      by 
        induction y using MulOpposite.rec 
        simp [smul_mul_assoc]⟩

example [Monoidₓ α] : Monoidₓ.toMulAction («expr ᵐᵒᵖ» α) = MulOpposite.mulAction α («expr ᵐᵒᵖ» α) :=
  rfl

/-- `monoid.to_opposite_mul_action` is faithful on cancellative monoids. -/
instance LeftCancelMonoid.to_has_faithful_opposite_scalar [LeftCancelMonoid α] : HasFaithfulScalar («expr ᵐᵒᵖ» α) α :=
  ⟨fun x y h => unop_injective$ mul_left_cancelₓ (h 1)⟩

/-- `monoid.to_opposite_mul_action` is faithful on nontrivial cancellative monoids with zero. -/
instance CancelMonoidWithZero.to_has_faithful_opposite_scalar [CancelMonoidWithZero α] [Nontrivial α] :
  HasFaithfulScalar («expr ᵐᵒᵖ» α) α :=
  ⟨fun x y h => unop_injective$ mul_left_cancel₀ one_ne_zero (h 1)⟩

