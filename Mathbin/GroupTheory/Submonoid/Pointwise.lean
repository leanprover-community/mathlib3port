import Mathbin.GroupTheory.Submonoid.Operations
import Mathbin.Algebra.Pointwise

/-! # Pointwise instances on `submonoid`s and `add_submonoid`s

This file provides:

* `submonoid.has_inv`
* `add_submonoid.has_neg`

and the actions

* `submonoid.pointwise_mul_action`
* `add_submonoid.pointwise_mul_action`

which matches the action of `mul_action_set`.

These are all available in the `pointwise` locale.

## Implementation notes

Most of the lemmas in this file are direct copies of lemmas from `algebra/pointwise.lean`.
While the statements of these lemmas are defeq, we repeat them here due to them not being
syntactically equal. Before adding new lemmas here, consider if they would also apply to the action
on `set`s.

-/


variable {α : Type _} {M : Type _} {G : Type _} {A : Type _} [Monoidₓ M] [AddMonoidₓ A]

namespace Submonoid

variable [Groupₓ G]

open_locale Pointwise

/-- The submonoid with every element inverted. -/
@[to_additive " The additive submonoid with every element negated. "]
protected def HasInv : HasInv (Submonoid G) where
  inv := fun S =>
    { Carrier := (S : Set G)⁻¹,
      one_mem' :=
        show (1 : G)⁻¹ ∈ S by
          rw [one_inv]
          exact S.one_mem,
      mul_mem' := fun a b ha : a⁻¹ ∈ S hb : b⁻¹ ∈ S =>
        show (a * b)⁻¹ ∈ S by
          rw [mul_inv_rev]
          exact S.mul_mem hb ha }

localized [Pointwise] attribute [instance] Submonoid.hasInv

open_locale Pointwise

@[simp, to_additive]
theorem coe_inv (S : Submonoid G) : ↑S⁻¹ = (S : Set G)⁻¹ :=
  rfl

@[simp, to_additive]
theorem mem_inv {g : G} {S : Submonoid G} : g ∈ S⁻¹ ↔ g⁻¹ ∈ S :=
  Iff.rfl

@[simp, to_additive]
protected theorem inv_invₓ (S : Submonoid G) : S⁻¹⁻¹ = S :=
  SetLike.coe_injective Set.inv_inv

@[simp, to_additive]
theorem inv_le_inv (S T : Submonoid G) : S⁻¹ ≤ T⁻¹ ↔ S ≤ T :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset_inv

@[to_additive]
theorem inv_le (S T : Submonoid G) : S⁻¹ ≤ T ↔ S ≤ T⁻¹ :=
  SetLike.coe_subset_coe.symm.trans Set.inv_subset

/-- `submonoid.has_inv` as an order isomorphism. -/
@[to_additive " `add_submonoid.has_neg` as an order isomorphism ", simps]
def inv_order_iso : Submonoid G ≃o Submonoid G where
  toFun := HasInv.inv
  invFun := HasInv.inv
  left_inv := Submonoid.inv_inv
  right_inv := Submonoid.inv_inv
  map_rel_iff' := inv_le_inv

@[to_additive]
theorem closure_inv (s : Set G) : closure (s⁻¹) = closure s⁻¹ := by
  apply le_antisymmₓ
  · rw [closure_le, coe_inv, ← Set.inv_subset, Set.inv_inv]
    exact subset_closure
    
  · rw [inv_le, closure_le, coe_inv, ← Set.inv_subset]
    exact subset_closure
    

@[simp, to_additive]
theorem inv_inf (S T : Submonoid G) : (S⊓T)⁻¹ = S⁻¹⊓T⁻¹ :=
  SetLike.coe_injective Set.inter_inv

@[simp, to_additive]
theorem inv_sup (S T : Submonoid G) : (S⊔T)⁻¹ = S⁻¹⊔T⁻¹ :=
  (inv_order_iso : Submonoid G ≃o Submonoid G).map_sup S T

@[simp, to_additive]
theorem inv_bot : (⊥ : Submonoid G)⁻¹ = ⊥ :=
  SetLike.coe_injective $ (Set.inv_singleton 1).trans $ congr_argₓ _ one_inv

@[simp, to_additive]
theorem inv_top : (⊤ : Submonoid G)⁻¹ = ⊤ :=
  SetLike.coe_injective $ Set.inv_univ

@[simp, to_additive]
theorem inv_infi {ι : Sort _} (S : ι → Submonoid G) : (⨅ i, S i)⁻¹ = ⨅ i, S i⁻¹ :=
  (inv_order_iso : Submonoid G ≃o Submonoid G).map_infi _

@[simp, to_additive]
theorem inv_supr {ι : Sort _} (S : ι → Submonoid G) : (⨆ i, S i)⁻¹ = ⨆ i, S i⁻¹ :=
  (inv_order_iso : Submonoid G ≃o Submonoid G).map_supr _

end Submonoid

namespace Submonoid

section Monoidₓ

variable [Monoidₓ α] [MulDistribMulAction α M]

/-- The action on a submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction α (Submonoid M) where
  smul := fun a S => S.map (MulDistribMulAction.toMonoidEnd _ _ a)
  one_smul := fun S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] Submonoid.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : Submonoid M) : ↑(a • S) = a • (S : Set M) :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (a : α) (S : Submonoid M) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set M))

theorem mem_smul_pointwise_iff_exists (m : M) (a : α) (S : Submonoid M) : m ∈ a • S ↔ ∃ s : M, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set M) ↔ _)

instance pointwise_central_scalar [MulDistribMulAction (αᵐᵒᵖ) M] [IsCentralScalar α M] :
    IsCentralScalar α (Submonoid M) :=
  ⟨fun a S => (congr_argₓ fun f => S.map f) $ MonoidHom.ext $ op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [MulDistribMulAction α M]

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

variable [GroupWithZeroₓ α] [MulDistribMulAction α M]

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

@[to_additive]
theorem mem_closure_inv {G : Type _} [Groupₓ G] (S : Set G) (x : G) :
    x ∈ Submonoid.closure (S⁻¹) ↔ x⁻¹ ∈ Submonoid.closure S := by
  rw [closure_inv, mem_inv]

end Submonoid

namespace AddSubmonoid

section Monoidₓ

variable [Monoidₓ α] [DistribMulAction α A]

/-- The action on an additive submonoid corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction α (AddSubmonoid A) where
  smul := fun a S => S.map (DistribMulAction.toAddMonoidEnd _ _ a)
  one_smul := fun S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_one _)).trans S.map_id
  mul_smul := fun a₁ a₂ S => (congr_argₓ (fun f => S.map f) (MonoidHom.map_mul _ _ _)).trans (S.map_map _ _).symm

localized [Pointwise] attribute [instance] AddSubmonoid.pointwiseMulAction

open_locale Pointwise

@[simp]
theorem coe_pointwise_smul (a : α) (S : AddSubmonoid A) : ↑(a • S) = a • (S : Set A) :=
  rfl

theorem smul_mem_pointwise_smul (m : A) (a : α) (S : AddSubmonoid A) : m ∈ S → a • m ∈ a • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ a • (S : Set A))

instance pointwise_central_scalar [DistribMulAction (αᵐᵒᵖ) A] [IsCentralScalar α A] :
    IsCentralScalar α (AddSubmonoid A) :=
  ⟨fun a S => (congr_argₓ fun f => S.map f) $ AddMonoidHom.ext $ op_smul_eq_smul _⟩

end Monoidₓ

section Groupₓ

variable [Groupₓ α] [DistribMulAction α A]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : α} {S : AddSubmonoid A} {x : A} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : α} {S : AddSubmonoid A} {x : A} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_smul_pointwise_iff_exists (m : A) (a : α) (S : AddSubmonoid A) : m ∈ a • S ↔ ∃ s : A, s ∈ S ∧ a • s = m :=
  (Set.mem_smul_set : m ∈ a • (S : Set A) ↔ _)

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

variable [GroupWithZeroₓ α] [DistribMulAction α A]

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

