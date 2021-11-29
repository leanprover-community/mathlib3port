import Mathbin.RingTheory.Subsemiring.Basic 
import Mathbin.Algebra.GroupRingAction 
import Mathbin.Algebra.Pointwise

/-! # Pointwise instances on `subsemiring`s

This file provides the action `subsemiring.pointwise_mul_action` which matches the action of
`mul_action_set`.

This actions is available in the `pointwise` locale.

## Implementation notes

This file is almost identical to `group_theory/submonoid/pointwise.lean`. Where possible, try to
keep them in sync.
-/


variable {M R : Type _}

namespace Subsemiring

section Monoidₓ

variable [Monoidₓ M] [Semiringₓ R] [MulSemiringAction M R]

/-- The action on a subsemiring corresponding to applying the action to every element.

This is available as an instance in the `pointwise` locale. -/
protected def pointwise_mul_action : MulAction M (Subsemiring R) :=
  { smul := fun a S => S.map (MulSemiringAction.toRingHom _ _ a),
    one_smul :=
      fun S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact one_smul M)).trans
          S.map_id,
    mul_smul :=
      fun a₁ a₂ S =>
        (congr_argₓ (fun f => S.map f)
              (RingHom.ext$
                by 
                  exact mul_smul _ _)).trans
          (S.map_map _ _).symm }

localized [Pointwise] attribute [instance] Subsemiring.pointwiseMulAction

open_locale Pointwise

theorem pointwise_smul_def {a : M} (S : Subsemiring R) : a • S = S.map (MulSemiringAction.toRingHom _ _ a) :=
  rfl

@[simp]
theorem coe_pointwise_smul (m : M) (S : Subsemiring R) : «expr↑ » (m • S) = m • (S : Set R) :=
  rfl

@[simp]
theorem pointwise_smul_to_add_submonoid (m : M) (S : Subsemiring R) : (m • S).toAddSubmonoid = m • S.to_add_submonoid :=
  rfl

theorem smul_mem_pointwise_smul (m : M) (r : R) (S : Subsemiring R) : r ∈ S → m • r ∈ m • S :=
  (Set.smul_mem_smul_set : _ → _ ∈ m • (S : Set R))

end Monoidₓ

section Groupₓ

variable [Groupₓ M] [Semiringₓ R] [MulSemiringAction M R]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff

theorem mem_pointwise_smul_iff_inv_smul_mem {a : M} {S : Subsemiring R} {x : R} : x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem

theorem mem_inv_pointwise_smul_iff {a : M} {S : Subsemiring R} {x : R} : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff {a : M} {S T : Subsemiring R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff

theorem pointwise_smul_subset_iff {a : M} {S T : Subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff

theorem subset_pointwise_smul_iff {a : M} {S T : Subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff

/-! TODO: add `equiv_smul` like we have for subgroup. -/


end Groupₓ

section GroupWithZeroₓ

variable [GroupWithZeroₓ M] [Semiringₓ R] [MulSemiringAction M R]

open_locale Pointwise

@[simp]
theorem smul_mem_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) : a • x ∈ a • S ↔ x ∈ S :=
  smul_mem_smul_set_iff₀ ha (S : Set R) x

theorem mem_pointwise_smul_iff_inv_smul_mem₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) :
  x ∈ a • S ↔ a⁻¹ • x ∈ S :=
  mem_smul_set_iff_inv_smul_mem₀ ha (S : Set R) x

theorem mem_inv_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) (S : Subsemiring R) (x : R) : x ∈ a⁻¹ • S ↔ a • x ∈ S :=
  mem_inv_smul_set_iff₀ ha (S : Set R) x

@[simp]
theorem pointwise_smul_le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} : a • S ≤ a • T ↔ S ≤ T :=
  set_smul_subset_set_smul_iff₀ ha

theorem pointwise_smul_le_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} : a • S ≤ T ↔ S ≤ a⁻¹ • T :=
  set_smul_subset_iff₀ ha

theorem le_pointwise_smul_iff₀ {a : M} (ha : a ≠ 0) {S T : Subsemiring R} : S ≤ a • T ↔ a⁻¹ • S ≤ T :=
  subset_set_smul_iff₀ ha

end GroupWithZeroₓ

end Subsemiring

