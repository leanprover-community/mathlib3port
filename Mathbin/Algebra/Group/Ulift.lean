import Mathbin.Data.Equiv.MulAdd

/-!
# `ulift` instances for groups and monoids

This file defines instances for group, monoid, semigroup and related structures on `ulift` types.

(Recall `ulift α` is just a "copy" of a type `α` in a higher universe.)

We use `tactic.pi_instance_derive_field`, even though it wasn't intended for this purpose,
which seems to work fine.

We also provide `ulift.mul_equiv : ulift R ≃* R` (and its additive analogue).
-/


universe u v

variable {α : Type u} {x y : Ulift.{v} α}

namespace Ulift

@[to_additive]
instance HasOne [HasOne α] : HasOne (Ulift α) :=
  ⟨⟨1⟩⟩

@[simp, to_additive]
theorem one_down [HasOne α] : (1 : Ulift α).down = 1 :=
  rfl

@[to_additive]
instance Mul [Mul α] : Mul (Ulift α) :=
  ⟨fun f g => ⟨f.down*g.down⟩⟩

@[simp, to_additive]
theorem mul_down [Mul α] : (x*y).down = x.down*y.down :=
  rfl

@[to_additive]
instance Div [Div α] : Div (Ulift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[simp, to_additive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
instance HasInv [HasInv α] : HasInv (Ulift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[simp, to_additive]
theorem inv_down [HasInv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

/-- 
The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def _root_.mul_equiv.ulift [Mul α] : Ulift α ≃* α :=
  { Equivₓ.ulift with map_mul' := fun x y => rfl }

@[to_additive]
instance Semigroupₓ [Semigroupₓ α] : Semigroupₓ (Ulift α) :=
  MulEquiv.ulift.Injective.Semigroup _ $ fun x y => rfl

@[to_additive]
instance CommSemigroupₓ [CommSemigroupₓ α] : CommSemigroupₓ (Ulift α) :=
  Equivₓ.ulift.Injective.CommSemigroup _ $ fun x y => rfl

@[to_additive]
instance MulOneClass [MulOneClass α] : MulOneClass (Ulift α) :=
  Equivₓ.ulift.Injective.MulOneClass _ rfl $ fun x y => rfl

@[to_additive HasVadd]
instance HasScalar {β : Type _} [HasScalar α β] : HasScalar α (Ulift β) :=
  ⟨fun n x => up (n • x.down)⟩

@[to_additive HasScalar, to_additive_reorder 1]
instance Pow {β : Type _} [Pow α β] : Pow (Ulift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive]
instance Monoidₓ [Monoidₓ α] : Monoidₓ (Ulift α) :=
  Equivₓ.ulift.Injective.monoidPow _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance CommMonoidₓ [CommMonoidₓ α] : CommMonoidₓ (Ulift α) :=
  { Ulift.monoid, Ulift.commSemigroup with }

@[to_additive]
instance DivInvMonoidₓ [DivInvMonoidₓ α] : DivInvMonoidₓ (Ulift α) :=
  Equivₓ.ulift.Injective.divInvMonoidPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]
instance Groupₓ [Groupₓ α] : Groupₓ (Ulift α) :=
  Equivₓ.ulift.Injective.groupPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance CommGroupₓ [CommGroupₓ α] : CommGroupₓ (Ulift α) :=
  { Ulift.group, Ulift.commSemigroup with }

@[to_additive AddLeftCancelSemigroup]
instance LeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (Ulift α) :=
  Equivₓ.ulift.Injective.LeftCancelSemigroup _ fun _ _ => rfl

@[to_additive AddRightCancelSemigroup]
instance RightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (Ulift α) :=
  Equivₓ.ulift.Injective.RightCancelSemigroup _ fun _ _ => rfl

@[to_additive AddLeftCancelMonoid]
instance LeftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.leftCancelSemigroup with }

@[to_additive AddRightCancelMonoid]
instance RightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.rightCancelSemigroup with }

@[to_additive AddCancelMonoid]
instance CancelMonoid [CancelMonoid α] : CancelMonoid (Ulift α) :=
  { Ulift.leftCancelMonoid, Ulift.rightCancelSemigroup with }

@[to_additive AddCancelMonoid]
instance CancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (Ulift α) :=
  { Ulift.cancelMonoid, Ulift.commSemigroup with }

end Ulift

