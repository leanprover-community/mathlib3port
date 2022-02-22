/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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
instance hasOne [One α] : One (Ulift α) :=
  ⟨⟨1⟩⟩

@[simp, to_additive]
theorem one_down [One α] : (1 : Ulift α).down = 1 :=
  rfl

@[to_additive]
instance hasMul [Mul α] : Mul (Ulift α) :=
  ⟨fun f g => ⟨f.down * g.down⟩⟩

@[simp, to_additive]
theorem mul_down [Mul α] : (x * y).down = x.down * y.down :=
  rfl

@[to_additive]
instance hasDiv [Div α] : Div (Ulift α) :=
  ⟨fun f g => ⟨f.down / g.down⟩⟩

@[simp, to_additive]
theorem div_down [Div α] : (x / y).down = x.down / y.down :=
  rfl

@[to_additive]
instance hasInv [Inv α] : Inv (Ulift α) :=
  ⟨fun f => ⟨f.down⁻¹⟩⟩

@[simp, to_additive]
theorem inv_down [Inv α] : x⁻¹.down = x.down⁻¹ :=
  rfl

/-- The multiplicative equivalence between `ulift α` and `α`.
-/
@[to_additive "The additive equivalence between `ulift α` and `α`."]
def _root_.mul_equiv.ulift [Mul α] : Ulift α ≃* α :=
  { Equivₓ.ulift with map_mul' := fun x y => rfl }

@[to_additive]
instance semigroup [Semigroupₓ α] : Semigroupₓ (Ulift α) :=
  (MulEquiv.ulift.Injective.Semigroup _) fun x y => rfl

@[to_additive]
instance commSemigroup [CommSemigroupₓ α] : CommSemigroupₓ (Ulift α) :=
  (Equivₓ.ulift.Injective.CommSemigroup _) fun x y => rfl

@[to_additive]
instance mulOneClass [MulOneClassₓ α] : MulOneClassₓ (Ulift α) :=
  (Equivₓ.ulift.Injective.MulOneClass _ rfl) fun x y => rfl

@[to_additive HasVadd]
instance hasScalar {β : Type _} [HasScalar α β] : HasScalar α (Ulift β) :=
  ⟨fun n x => up (n • x.down)⟩

@[to_additive HasScalar, to_additive_reorder 1]
instance hasPow {β : Type _} [Pow α β] : Pow (Ulift α) β :=
  ⟨fun x n => up (x.down ^ n)⟩

@[to_additive]
instance monoid [Monoidₓ α] : Monoidₓ (Ulift α) :=
  Equivₓ.ulift.Injective.monoidPow _ rfl (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance commMonoid [CommMonoidₓ α] : CommMonoidₓ (Ulift α) :=
  { Ulift.monoid, Ulift.commSemigroup with }

@[to_additive]
instance divInvMonoid [DivInvMonoidₓ α] : DivInvMonoidₓ (Ulift α) :=
  Equivₓ.ulift.Injective.divInvMonoidPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    fun _ _ => rfl

@[to_additive]
instance group [Groupₓ α] : Groupₓ (Ulift α) :=
  Equivₓ.ulift.Injective.groupPow _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

@[to_additive]
instance commGroup [CommGroupₓ α] : CommGroupₓ (Ulift α) :=
  { Ulift.group, Ulift.commSemigroup with }

@[to_additive AddLeftCancelSemigroup]
instance leftCancelSemigroup [LeftCancelSemigroup α] : LeftCancelSemigroup (Ulift α) :=
  Equivₓ.ulift.Injective.LeftCancelSemigroup _ fun _ _ => rfl

@[to_additive AddRightCancelSemigroup]
instance rightCancelSemigroup [RightCancelSemigroup α] : RightCancelSemigroup (Ulift α) :=
  Equivₓ.ulift.Injective.RightCancelSemigroup _ fun _ _ => rfl

@[to_additive AddLeftCancelMonoid]
instance leftCancelMonoid [LeftCancelMonoid α] : LeftCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.leftCancelSemigroup with }

@[to_additive AddRightCancelMonoid]
instance rightCancelMonoid [RightCancelMonoid α] : RightCancelMonoid (Ulift α) :=
  { Ulift.monoid, Ulift.rightCancelSemigroup with }

@[to_additive AddCancelMonoid]
instance cancelMonoid [CancelMonoid α] : CancelMonoid (Ulift α) :=
  { Ulift.leftCancelMonoid, Ulift.rightCancelSemigroup with }

@[to_additive AddCancelMonoid]
instance cancelCommMonoid [CancelCommMonoid α] : CancelCommMonoid (Ulift α) :=
  { Ulift.cancelMonoid, Ulift.commSemigroup with }

instance nontrivial [Nontrivial α] : Nontrivial (Ulift α) :=
  Equivₓ.ulift.symm.Injective.Nontrivial

-- TODO we don't do `ordered_cancel_comm_monoid` or `ordered_comm_group`
-- We'd need to add instances for `ulift` in `order.basic`.
end Ulift

