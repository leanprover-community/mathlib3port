import Mathbin.GroupTheory.Submonoid.Operations 
import Mathbin.Algebra.Pointwise

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

This file provides the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These actions are available in the `pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/


variable{α : Type _}{M : Type _}{A : Type _}[Monoidₓ M][AddMonoidₓ A]

namespace Submonoid

section Monoidₓ

variable[Monoidₓ α][MulDistribMulAction α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction α (Submonoid M) :=
  { smul := fun a S => S.map (MulDistribMulAction.toMonoidEnd _ _ a),
    one_smul := fun S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id,
    mul_smul := fun a₁ a₂ S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] Submonoid.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : «expr↑ » (a • S) = a • (S : Set M) :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

end Monoidₓ

section Groupₓ

variable[Groupₓ α][MulDistribMulAction α M]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : Submonoid M} {x : M} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : Submonoid M} {x : M} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : α} {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : α} {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

end Groupₓ

section GroupWithZeroₓ

variable[GroupWithZeroₓ α][MulDistribMulAction α M]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set M) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set M) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : Submonoid M) (x : M) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set M) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : Submonoid M} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

open_locale Pointwise

@[toAdditive]
theorem mem_closure_inv {G : Type _} [Groupₓ G] (S : Set G) (x : G) :
  x ∈ Submonoid.closure (S⁻¹) ↔ x⁻¹ ∈ Submonoid.closure S :=
  by 
    suffices  : ∀ S : Set G x : G, x ∈ Submonoid.closure (S⁻¹) → x⁻¹ ∈ Submonoid.closure S
    ·
      refine' ⟨this S x, _⟩
      have  := this (S⁻¹) (x⁻¹)
      rwa [inv_invₓ, Set.inv_inv] at this 
    intro S x hx 
    refine' Submonoid.closure_induction hx (fun x hx => _) _ fun x y hx hy => _
    ·
      exact Submonoid.subset_closure (set.mem_inv.mp hx)
    ·
      rw [one_inv]
      exact Submonoid.one_mem _
    ·
      rw [mul_inv_rev x y]
      exact Submonoid.mul_mem _ hy hx

end Submonoid

namespace AddSubmonoid

section Monoidₓ

variable[Monoidₓ α][DistribMulAction α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction α (AddSubmonoid A) :=
  { smul := fun a S => S.map (DistribMulAction.toAddMonoidEnd _ _ a),
    one_smul := fun S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id,
    mul_smul := fun a₁ a₂ S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : AddSubmonoid A) : «expr↑ » (a • S) = a • (S : Set A) :=
  rfl

theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubmonoid A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

end Monoidₓ

section Groupₓ

variable[Groupₓ α][DistribMulAction α A]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_le_iff {a : α} {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem le_pointwise_smul_iff {a : α} {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

end Groupₓ

section GroupWithZeroₓ

variable[GroupWithZeroₓ α][DistribMulAction α A]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set A) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set A) x

theorem mem_inv_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) (S : AddSubmonoid A) (x : A) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set A) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : α} (ha : a ≠ 0) {S T : AddSubmonoid A} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

open_locale Pointwise

end AddSubmonoid

