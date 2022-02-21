/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.LinearAlgebra.Basic

/-! # Pointwise instances on `submodule`s

This file provides the actions

* `submodule.pointwise_distrib_mul_action`
* `submodule.pointwise_mul_action_with_zero`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.
-/


namespace Submodule

variable {α : Type _} {R : Type _} {M : Type _}

variable [Semiringₓ R] [AddCommMonoidₓ M] [Module R M]

instance pointwiseAddCommMonoid : AddCommMonoidₓ (Submodule R M) where
  add := (·⊔·)
  add_assoc := fun _ _ _ => sup_assoc
  zero := ⊥
  zero_add := fun _ => bot_sup_eq
  add_zero := fun _ => sup_bot_eq
  add_comm := fun _ _ => sup_comm

@[simp]
theorem add_eq_sup (p q : Submodule R M) : p + q = p⊔q :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

section

variable [Monoidₓ α] [DistribMulAction α M] [SmulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwiseDistribMulAction : DistribMulAction α (Submodule R M) where
  smul := fun a S => S.map (DistribMulAction.toLinearMap _ _ a)
  one_smul := fun S => (congr_argₓ (fun f => S.map f) (LinearMap.ext <| one_smul α)).trans S.map_id
  mul_smul := fun a₁ a₂ S =>
    (congr_argₓ (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| mul_smul _ _)).trans (S.map_comp _ _)
  smul_zero := fun a => map_bot _
  smul_add := fun a S₁ S₂ => map_sup _ _ _

localized [Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : ↑(a • S) = a • (S : Set M) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (a : α) (S : Submodule R M) : (a • S).toAddSubmonoid = a • S.toAddSubmonoid :=
  rfl

@[simp]
theorem pointwise_smul_to_add_subgroup {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [DistribMulAction α M] [Module R M]
    [SmulCommClass α R M] (a : α) (S : Submodule R M) : (a • S).toAddSubgroup = a • S.toAddSubgroup :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

instance pointwise_central_scalar [DistribMulAction αᵐᵒᵖ M] [SmulCommClass αᵐᵒᵖ R M] [IsCentralScalar α M] :
    IsCentralScalar α (Submodule R M) :=
  ⟨fun a S => (congr_argₓ fun f => S.map f) <| LinearMap.ext <| op_smul_eq_smul _⟩

@[simp]
theorem smul_le_self_of_tower {α : Type _} [Semiringₓ α] [Module α R] [Module α M] [SmulCommClass α R M]
    [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S := by
  rintro y ⟨x, hx, rfl⟩
  exact smul_of_tower_mem _ a hx

end

section

variable [Semiringₓ α] [Module α M] [SmulCommClass α R M]

/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `submodule.pointwise_distrib_mul_action`. Note that `add_smul` does
not hold so this cannot be stated as a `module`. -/
protected def pointwiseMulActionWithZero : MulActionWithZero α (Submodule R M) :=
  { Submodule.pointwiseDistribMulAction with
    zero_smul := fun S => (congr_argₓ (fun f : M →ₗ[R] M => S.map f) (LinearMap.ext <| zero_smul α)).trans S.map_zero }

localized [Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end

end Submodule

