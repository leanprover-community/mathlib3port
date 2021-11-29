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

variable{α : Type _}{R : Type _}{M : Type _}

variable[Semiringₓ R][AddCommMonoidₓ M][Module R M]

instance pointwise_add_comm_monoid : AddCommMonoidₓ (Submodule R M) :=
  { add := ·⊔·, add_assoc := fun _ _ _ => sup_assoc, zero := ⊥, zero_add := fun _ => bot_sup_eq,
    add_zero := fun _ => sup_bot_eq, add_comm := fun _ _ => sup_comm }

@[simp]
theorem add_eq_sup (p q : Submodule R M) : (p+q) = p⊔q :=
  rfl

@[simp]
theorem zero_eq_bot : (0 : Submodule R M) = ⊥ :=
  rfl

section 

variable[Monoidₓ α][DistribMulAction α M][SmulCommClass α R M]

-- error in Algebra.Module.SubmodulePointwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected
def pointwise_distrib_mul_action : distrib_mul_action α (submodule R M) :=
{ smul := λ a S, S.map (distrib_mul_action.to_linear_map _ _ a),
  one_smul := λ S, (congr_arg (λ f, S.map f) «expr $ »(linear_map.ext, by exact [expr one_smul α])).trans S.map_id,
  mul_smul := λ
  a₁
  a₂
  S, (congr_arg (λ
    f : «expr →ₗ[ ] »(M, R, M), S.map f) «expr $ »(linear_map.ext, by exact [expr mul_smul _ _])).trans (S.map_comp _ _),
  smul_zero := λ a, map_bot _,
  smul_add := λ a S₁ S₂, map_sup _ _ _ }

localized [Pointwise] attribute [instance] Submodule.pointwiseDistribMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submodule R M) : «expr↑ » (a • S) = a • (S : Set M) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (a : α) (S : Submodule R M) : (a • S).toAddSubmonoid = a • S.to_add_submonoid :=
  rfl

@[simp]
theorem pointwise_smul_to_add_subgroup {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [DistribMulAction α M] [Module R M]
  [SmulCommClass α R M] (a : α) (S : Submodule R M) : (a • S).toAddSubgroup = a • S.to_add_subgroup :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submodule R M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

@[simp]
theorem smul_le_self_of_tower {α : Type _} [Semiringₓ α] [Module α R] [Module α M] [SmulCommClass α R M]
  [IsScalarTower α R M] (a : α) (S : Submodule R M) : a • S ≤ S :=
  by 
    rintro y ⟨x, hx, rfl⟩
    exact smul_of_tower_mem _ a hx

end 

section 

variable[Semiringₓ α][Module α M][SmulCommClass α R M]

-- error in Algebra.Module.SubmodulePointwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- The action on a submodule corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale.

This is a stronger version of `submodule.pointwise_distrib_mul_action`. Note that `add_smul` does
not hold so this cannot be stated as a `module`. -/
protected
def pointwise_mul_action_with_zero : mul_action_with_zero α (submodule R M) :=
{ zero_smul := λ
  S, (congr_arg (λ
    f : «expr →ₗ[ ] »(M, R, M), S.map f) «expr $ »(linear_map.ext, by exact [expr zero_smul α])).trans S.map_zero,
  ..submodule.pointwise_distrib_mul_action }

localized [Pointwise] attribute [instance] Submodule.pointwiseMulActionWithZero

end 

end Submodule

