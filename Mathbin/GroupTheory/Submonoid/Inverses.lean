/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module group_theory.submonoid.inverses
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.GroupTheory.Submonoid.Pointwise

/-!

# Submonoid of inverses

Given a submonoid `N` of a monoid `M`, we define the submonoid `N.left_inv` as the submonoid of
left inverses of `N`. When `M` is commutative, we may define `from_comm_left_inv : N.left_inv →* N`
since the inverses are unique. When `N ≤ is_unit.submonoid M`, this is precisely
the pointwise inverse of `N`, and we may define `left_inv_equiv : S.left_inv ≃* S`.

For the pointwise inverse of submonoids of groups, please refer to
`group_theory.submonoid.pointwise`.

## TODO

Define the submonoid of right inverses and two-sided inverses.
See the comments of #10679 for a possible implementation.

-/


variable {M : Type _}

namespace Submonoid

@[to_additive]
noncomputable instance [Monoid M] : Group (IsUnit.submonoid M) :=
  {
    show Monoid (IsUnit.submonoid M) by
      infer_instance with
    inv := fun x => ⟨_, x.Prop.Unit⁻¹.IsUnit⟩
    mul_left_inv := fun x => Subtype.eq x.Prop.Unit.inv_val }

@[to_additive]
noncomputable instance [CommMonoid M] : CommGroup (IsUnit.submonoid M) :=
  { show Group (IsUnit.submonoid M) by infer_instance with mul_comm := fun a b => mul_comm a b }

@[to_additive]
theorem IsUnit.Submonoid.coe_inv [Monoid M] (x : IsUnit.submonoid M) :
    ↑x⁻¹ = (↑x.Prop.Unit⁻¹ : M) :=
  rfl
#align submonoid.is_unit.submonoid.coe_inv Submonoid.IsUnit.Submonoid.coe_inv

section Monoid

variable [Monoid M] (S : Submonoid M)

/-- `S.left_inv` is the submonoid containing all the left inverses of `S`. -/
@[to_additive
      "`S.left_neg` is the additive submonoid containing all the left additive inverses\nof `S`."]
def leftInv : Submonoid M where
  carrier := { x : M | ∃ y : S, x * y = 1 }
  one_mem' := ⟨1, mul_one 1⟩
  mul_mem' := fun a b ⟨a', ha⟩ ⟨b', hb⟩ =>
    ⟨b' * a', by rw [coe_mul, ← mul_assoc, mul_assoc a, hb, mul_one, ha]⟩
#align submonoid.left_inv Submonoid.leftInv

@[to_additive]
theorem left_inv_left_inv_le : S.left_inv.left_inv ≤ S :=
  by
  rintro x ⟨⟨y, z, h₁⟩, h₂ : x * y = 1⟩
  convert z.prop
  rw [← mul_one x, ← h₁, ← mul_assoc, h₂, one_mul]
#align submonoid.left_inv_left_inv_le Submonoid.left_inv_left_inv_le

@[to_additive]
theorem unit_mem_left_inv (x : Mˣ) (hx : (x : M) ∈ S) : ((x⁻¹ : _) : M) ∈ S.left_inv :=
  ⟨⟨x, hx⟩, x.inv_val⟩
#align submonoid.unit_mem_left_inv Submonoid.unit_mem_left_inv

@[to_additive]
theorem left_inv_left_inv_eq (hS : S ≤ IsUnit.submonoid M) : S.left_inv.left_inv = S :=
  by
  refine' le_antisymm S.left_inv_left_inv_le _
  intro x hx
  have : x = ((hS hx).Unit⁻¹⁻¹ : Mˣ) :=
    by
    rw [inv_inv (hS hx).Unit]
    rfl
  rw [this]
  exact S.left_inv.unit_mem_left_inv _ (S.unit_mem_left_inv _ hx)
#align submonoid.left_inv_left_inv_eq Submonoid.left_inv_left_inv_eq

/-- The function from `S.left_inv` to `S` sending an element to its right inverse in `S`.
This is a `monoid_hom` when `M` is commutative. -/
@[to_additive
      "The function from `S.left_add` to `S` sending an element to its right additive\ninverse in `S`. This is an `add_monoid_hom` when `M` is commutative."]
noncomputable def fromLeftInv : S.left_inv → S := fun x => x.Prop.some
#align submonoid.from_left_inv Submonoid.fromLeftInv

@[simp, to_additive]
theorem mul_from_left_inv (x : S.left_inv) : (x : M) * S.fromLeftInv x = 1 :=
  x.Prop.some_spec
#align submonoid.mul_from_left_inv Submonoid.mul_from_left_inv

@[simp, to_additive]
theorem from_left_inv_one : S.fromLeftInv 1 = 1 :=
  (one_mul _).symm.trans (Subtype.eq <| S.mul_from_left_inv 1)
#align submonoid.from_left_inv_one Submonoid.from_left_inv_one

end Monoid

section CommMonoid

variable [CommMonoid M] (S : Submonoid M)

@[simp, to_additive]
theorem from_left_inv_mul (x : S.left_inv) : (S.fromLeftInv x : M) * x = 1 := by
  rw [mul_comm, mul_from_left_inv]
#align submonoid.from_left_inv_mul Submonoid.from_left_inv_mul

@[to_additive]
theorem left_inv_le_is_unit : S.left_inv ≤ IsUnit.submonoid M := fun x ⟨y, hx⟩ =>
  ⟨⟨x, y, hx, mul_comm x y ▸ hx⟩, rfl⟩
#align submonoid.left_inv_le_is_unit Submonoid.left_inv_le_is_unit

@[to_additive]
theorem from_left_inv_eq_iff (a : S.left_inv) (b : M) :
    (S.fromLeftInv a : M) = b ↔ (a : M) * b = 1 := by
  rw [← IsUnit.mul_right_inj (left_inv_le_is_unit _ a.prop), S.mul_from_left_inv, eq_comm]
#align submonoid.from_left_inv_eq_iff Submonoid.from_left_inv_eq_iff

/-- The `monoid_hom` from `S.left_inv` to `S` sending an element to its right inverse in `S`. -/
@[to_additive
      "The `add_monoid_hom` from `S.left_neg` to `S` sending an element to its\nright additive inverse in `S`.",
  simps]
noncomputable def fromCommLeftInv : S.left_inv →* S
    where
  toFun := S.fromLeftInv
  map_one' := S.from_left_inv_one
  map_mul' x y :=
    Subtype.ext <| by
      rw [from_left_inv_eq_iff, mul_comm x, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, ←
        mul_assoc (x : M), mul_from_left_inv, one_mul, mul_from_left_inv]
#align submonoid.from_comm_left_inv Submonoid.fromCommLeftInv

variable (hS : S ≤ IsUnit.submonoid M)

include hS

/-- The submonoid of pointwise inverse of `S` is `mul_equiv` to `S`. -/
@[to_additive "The additive submonoid of pointwise additive inverse of `S` is\n`add_equiv` to `S`.",
  simps apply]
noncomputable def leftInvEquiv : S.left_inv ≃* S :=
  {
    S.fromCommLeftInv with
    invFun := fun x => by
      choose x' hx using hS x.prop
      exact ⟨x'.inv, x, hx ▸ x'.inv_val⟩
    left_inv := fun x =>
      Subtype.eq <| by
        dsimp; generalize_proofs h; rw [← h.some.mul_left_inj]
        exact h.some.inv_val.trans ((S.mul_from_left_inv x).symm.trans (by rw [h.some_spec]))
    right_inv := fun x => by
      dsimp
      ext
      rw [from_left_inv_eq_iff]
      convert (hS x.prop).some.inv_val
      exact (hS x.prop).some_spec.symm }
#align submonoid.left_inv_equiv Submonoid.leftInvEquiv

@[simp, to_additive]
theorem from_left_inv_left_inv_equiv_symm (x : S) :
    S.fromLeftInv ((S.leftInvEquiv hS).symm x) = x :=
  (S.leftInvEquiv hS).right_inv x
#align submonoid.from_left_inv_left_inv_equiv_symm Submonoid.from_left_inv_left_inv_equiv_symm

@[simp, to_additive]
theorem left_inv_equiv_symm_from_left_inv (x : S.left_inv) :
    (S.leftInvEquiv hS).symm (S.fromLeftInv x) = x :=
  (S.leftInvEquiv hS).left_inv x
#align submonoid.left_inv_equiv_symm_from_left_inv Submonoid.left_inv_equiv_symm_from_left_inv

@[to_additive]
theorem left_inv_equiv_mul (x : S.left_inv) : (S.leftInvEquiv hS x : M) * x = 1 := by simp
#align submonoid.left_inv_equiv_mul Submonoid.left_inv_equiv_mul

@[to_additive]
theorem mul_left_inv_equiv (x : S.left_inv) : (x : M) * S.leftInvEquiv hS x = 1 := by simp
#align submonoid.mul_left_inv_equiv Submonoid.mul_left_inv_equiv

@[simp, to_additive]
theorem left_inv_equiv_symm_mul (x : S) : ((S.leftInvEquiv hS).symm x : M) * x = 1 :=
  by
  convert S.mul_left_inv_equiv hS ((S.left_inv_equiv hS).symm x)
  simp
#align submonoid.left_inv_equiv_symm_mul Submonoid.left_inv_equiv_symm_mul

@[simp, to_additive]
theorem mul_left_inv_equiv_symm (x : S) : (x : M) * (S.leftInvEquiv hS).symm x = 1 :=
  by
  convert S.left_inv_equiv_mul hS ((S.left_inv_equiv hS).symm x)
  simp
#align submonoid.mul_left_inv_equiv_symm Submonoid.mul_left_inv_equiv_symm

end CommMonoid

section Group

variable [Group M] (S : Submonoid M)

open Pointwise

@[to_additive]
theorem left_inv_eq_inv : S.left_inv = S⁻¹ :=
  Submonoid.ext fun x =>
    ⟨fun h => Submonoid.mem_inv.mpr ((inv_eq_of_mul_eq_one_right h.some_spec).symm ▸ h.some.Prop),
      fun h => ⟨⟨_, h⟩, mul_right_inv _⟩⟩
#align submonoid.left_inv_eq_inv Submonoid.left_inv_eq_inv

@[simp, to_additive]
theorem from_left_inv_eq_inv (x : S.left_inv) : (S.fromLeftInv x : M) = x⁻¹ := by
  rw [← mul_right_inj (x : M), mul_right_inv, mul_from_left_inv]
#align submonoid.from_left_inv_eq_inv Submonoid.from_left_inv_eq_inv

end Group

section CommGroup

variable [CommGroup M] (S : Submonoid M) (hS : S ≤ IsUnit.submonoid M)

@[simp, to_additive]
theorem left_inv_equiv_symm_eq_inv (x : S) : ((S.leftInvEquiv hS).symm x : M) = x⁻¹ := by
  rw [← mul_right_inj (x : M), mul_right_inv, mul_left_inv_equiv_symm]
#align submonoid.left_inv_equiv_symm_eq_inv Submonoid.left_inv_equiv_symm_eq_inv

end CommGroup

end Submonoid

