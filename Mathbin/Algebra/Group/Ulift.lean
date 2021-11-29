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

@[toAdditive]
instance HasOne [HasOne α] : HasOne (Ulift α) :=
  ⟨⟨1⟩⟩

@[simp, toAdditive]
theorem one_down [HasOne α] : (1 : Ulift α).down = 1 :=
  rfl

@[toAdditive]
instance Mul [Mul α] : Mul (Ulift α) :=
  ⟨fun f g => ⟨f.down*g.down⟩⟩

@[simp, toAdditive]
theorem mul_down [Mul α] : (x*y).down = x.down*y.down :=
  rfl

@[toAdditive]
instance Div [Div α] : Div (Ulift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[simp, toAdditive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[toAdditive]
instance HasInv [HasInv α] : HasInv (Ulift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[simp, toAdditive]
theorem inv_down [HasInv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

/--
The multiplicative equivalence between `ulift α` and `α`.
-/
@[toAdditive "The additive equivalence between `ulift α` and `α`."]
def _root_.mul_equiv.ulift [Mul α] : Ulift α ≃* α :=
  { Equiv.ulift with map_mul' := fun x y => rfl }

@[toAdditive]
instance Semigroupₓ [Semigroupₓ α] : Semigroupₓ (Ulift α) :=
  MulEquiv.ulift.Injective.Semigroup _$ fun x y => rfl

@[toAdditive]
instance CommSemigroupₓ [CommSemigroupₓ α] : CommSemigroupₓ (Ulift α) :=
  Equiv.ulift.Injective.CommSemigroup _$ fun x y => rfl

@[toAdditive]
instance MulOneClass [MulOneClass α] : MulOneClass (Ulift α) :=
  Equiv.ulift.Injective.MulOneClass _ rfl$ fun x y => rfl

@[toAdditive HasVadd]
instance HasScalar {β : Type _} [HasScalar α β] : HasScalar α (Ulift β) :=
  ⟨fun n x => up (n • x.down)⟩

@[toAdditive HasScalar, toAdditiveReorder 1]
instance Pow {β : Type _} [Pow α β] : Pow (Ulift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[toAdditive]
instance Monoidₓ [Monoidₓ α] : Monoidₓ (Ulift α) :=
  Equiv.ulift.Injective.monoidPow _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[toAdditive]
instance CommMonoidₓ [CommMonoidₓ α] : CommMonoidₓ (Ulift α) :=
  { Ulift.monoid, Ulift.commSemigroup with  }

@[toAdditive]
instance DivInvMonoidₓ [DivInvMonoidₓ α] : DivInvMonoidₓ (Ulift α) :=
  Equiv.ulift.Injective.divInvMonoidPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

@[toAdditive]
instance Groupₓ [Groupₓ α] : Groupₓ (Ulift α) :=
  Equiv.ulift.Injective.groupPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[toAdditive]
instance CommGroupₓ [CommGroupₓ α] : CommGroupₓ (Ulift α) :=
  { Ulift.group, Ulift.commSemigroup with  }

@[toAdditive AddLeftCancelSemigroup]
instance LeftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (Ulift α) :=
  Equiv.ulift.Injective.LeftCancelSemigroup _ fun _ _ => rfl

@[toAdditive AddRightCancelSemigroup]
instance RightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (Ulift α) :=
  Equiv.ulift.Injective.RightCancelSemigroup _ fun _ _ => rfl

@[toAdditive AddLeftCancelMonoid]
instance LeftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.leftCancelSemigroup with  }

@[toAdditive AddRightCancelMonoid]
instance RightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.rightCancelSemigroup with  }

@[toAdditive AddCancelMonoid]
instance CancelMonoid [CancelMonoid α] : CancelMonoid (Ulift α) :=
  { Ulift.leftCancelMonoid, Ulift.rightCancelSemigroup with  }

@[toAdditive AddCancelMonoid]
instance CancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (Ulift α) :=
  { Ulift.cancelMonoid, Ulift.commSemigroup with  }

end Ulift

