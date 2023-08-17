/-
Copyright (c) 2017 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johannes Hölzl, Chris Hughes, Jens Wagemaker, Jon Eugster
-/
import Mathbin.Algebra.Group.Basic
import Mathbin.Logic.Unique
import Mathbin.Tactic.Nontriviality

#align_import algebra.group.units from "leanprover-community/mathlib"@"e8638a0fcaf73e4500469f368ef9494e495099b3"

/-!
# Units (i.e., invertible elements) of a monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An element of a `monoid` is a unit if it has a two-sided inverse.

## Main declarations

* `units M`: the group of units (i.e., invertible elements) of a monoid.
* `is_unit x`: a predicate asserting that `x` is a unit (i.e., invertible element) of a monoid.

For both declarations, there is an additive counterpart: `add_units` and `is_add_unit`.

## Notation

We provide `Mˣ` as notation for `units M`,
resembling the notation $R^{\times}$ for the units of a ring, which is common in mathematics.

-/


open Function

universe u

variable {α : Type u}

#print Units /-
/-- Units of a `monoid`, bundled version. Notation: `αˣ`.

An element of a `monoid` is a unit if it has a two-sided inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_unit`. -/
structure Units (α : Type u) [Monoid α] where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1
#align units Units
-/

postfix:1024 "ˣ" => Units

#print AddUnits /-
-- We don't provide notation for the additive version, because its use is somewhat rare.
/-- Units of an `add_monoid`, bundled version.

An element of an `add_monoid` is a unit if it has a two-sided additive inverse.
This version bundles the inverse element so that it can be computed.
For a predicate see `is_add_unit`. -/
structure AddUnits (α : Type u) [AddMonoid α] where
  val : α
  neg : α
  val_neg : val + neg = 0
  neg_val : neg + val = 0
#align add_units AddUnits
-/

attribute [to_additive] Units

section HasElem

#print unique_one /-
@[to_additive]
theorem unique_one {α : Type _} [Unique α] [One α] : default = (1 : α) :=
  Unique.default_eq 1
#align unique_has_one unique_one
#align unique_has_zero unique_zero
-/

end HasElem

namespace Units

variable [Monoid α]

@[to_additive]
instance : Coe αˣ α :=
  ⟨val⟩

@[to_additive]
instance : Inv αˣ :=
  ⟨fun u => ⟨u.2, u.1, u.4, u.3⟩⟩

/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection] "]
def Simps.coe (u : αˣ) : α :=
  u
#align units.simps.coe Units.Simps.coe
#align add_units.simps.coe AddUnits.Simps.coe

/-- See Note [custom simps projection] -/
@[to_additive " See Note [custom simps projection] "]
def Simps.coeInv (u : αˣ) : α :=
  ↑u⁻¹
#align units.simps.coe_inv Units.Simps.coeInv
#align add_units.simps.coe_neg AddUnits.Simps.coeNeg

initialize_simps_projections Units (val → coe, as_prefix coe, inv → coeInv, as_prefix coeInv)

initialize_simps_projections AddUnits (val → coe, as_prefix coe, neg → coeNeg, as_prefix coeNeg)

#print Units.val_mk /-
@[simp, to_additive]
theorem val_mk (a : α) (b h₁ h₂) : ↑(Units.mk a b h₁ h₂) = a :=
  rfl
#align units.coe_mk Units.val_mk
#align add_units.coe_mk AddUnits.val_mk
-/

#print Units.ext /-
@[ext, to_additive]
theorem ext : Function.Injective (coe : αˣ → α)
  | ⟨v, i₁, vi₁, iv₁⟩, ⟨v', i₂, vi₂, iv₂⟩, e => by
    change v = v' at e  <;> subst v' <;> congr <;>
      simpa only [iv₂, vi₁, one_mul, mul_one] using mul_assoc i₂ v i₁
#align units.ext Units.ext
#align add_units.ext AddUnits.ext
-/

#print Units.eq_iff /-
@[norm_cast, to_additive]
theorem eq_iff {a b : αˣ} : (a : α) = b ↔ a = b :=
  ext.eq_iff
#align units.eq_iff Units.eq_iff
#align add_units.eq_iff AddUnits.eq_iff
-/

#print Units.ext_iff /-
@[to_additive]
theorem ext_iff {a b : αˣ} : a = b ↔ (a : α) = b :=
  eq_iff.symm
#align units.ext_iff Units.ext_iff
#align add_units.ext_iff AddUnits.ext_iff
-/

@[to_additive]
instance [DecidableEq α] : DecidableEq αˣ := fun a b => decidable_of_iff' _ ext_iff

#print Units.mk_val /-
@[simp, to_additive]
theorem mk_val (u : αˣ) (y h₁ h₂) : mk (u : α) y h₁ h₂ = u :=
  ext rfl
#align units.mk_coe Units.mk_val
#align add_units.mk_coe AddUnits.mk_val
-/

#print Units.copy /-
/-- Copy a unit, adjusting definition equalities. -/
@[to_additive "Copy an `add_unit`, adjusting definitional equalities.", simps]
def copy (u : αˣ) (val : α) (hv : val = u) (inv : α) (hi : inv = ↑u⁻¹) : αˣ :=
  { val
    inv
    inv_val := hv.symm ▸ hi.symm ▸ u.inv_val
    val_inv := hv.symm ▸ hi.symm ▸ u.val_inv }
#align units.copy Units.copy
#align add_units.copy AddUnits.copy
-/

#print Units.copy_eq /-
@[to_additive]
theorem copy_eq (u : αˣ) (val hv inv hi) : u.copy val hv inv hi = u :=
  ext hv
#align units.copy_eq Units.copy_eq
#align add_units.copy_eq AddUnits.copy_eq
-/

@[to_additive]
instance : MulOneClass αˣ
    where
  mul u₁ u₂ :=
    ⟨u₁.val * u₂.val, u₂.inv * u₁.inv, by
      rw [mul_assoc, ← mul_assoc u₂.val, val_inv, one_mul, val_inv], by
      rw [mul_assoc, ← mul_assoc u₁.inv, inv_val, one_mul, inv_val]⟩
  one := ⟨1, 1, one_mul 1, one_mul 1⟩
  one_mul u := ext <| one_mul u
  mul_one u := ext <| mul_one u

/-- Units of a monoid form a group. -/
@[to_additive "Additive units of an additive monoid form an additive group."]
instance : Group αˣ :=
  { Units.mulOneClass with
    mul := (· * ·)
    one := 1
    mul_assoc := fun u₁ u₂ u₃ => ext <| mul_assoc u₁ u₂ u₃
    inv := Inv.inv
    hMul_left_inv := fun u => ext u.inv_val }

@[to_additive]
instance {α} [CommMonoid α] : CommGroup αˣ :=
  { Units.group with mul_comm := fun u₁ u₂ => ext <| mul_comm _ _ }

@[to_additive]
instance : Inhabited αˣ :=
  ⟨1⟩

@[to_additive]
instance [Repr α] : Repr αˣ :=
  ⟨repr ∘ val⟩

variable (a b c : αˣ) {u : αˣ}

#print Units.val_mul /-
@[simp, norm_cast, to_additive]
theorem val_mul : (↑(a * b) : α) = a * b :=
  rfl
#align units.coe_mul Units.val_mul
#align add_units.coe_add AddUnits.val_add
-/

#print Units.val_one /-
@[simp, norm_cast, to_additive]
theorem val_one : ((1 : αˣ) : α) = 1 :=
  rfl
#align units.coe_one Units.val_one
#align add_units.coe_zero AddUnits.val_zero
-/

#print Units.val_eq_one /-
@[simp, norm_cast, to_additive]
theorem val_eq_one {a : αˣ} : (a : α) = 1 ↔ a = 1 := by rw [← Units.val_one, eq_iff]
#align units.coe_eq_one Units.val_eq_one
#align add_units.coe_eq_zero AddUnits.val_eq_zero
-/

#print Units.inv_mk /-
@[simp, to_additive]
theorem inv_mk (x y : α) (h₁ h₂) : (mk x y h₁ h₂)⁻¹ = mk y x h₂ h₁ :=
  rfl
#align units.inv_mk Units.inv_mk
#align add_units.neg_mk AddUnits.neg_mk
-/

@[simp, to_additive]
theorem val_eq_coe : a.val = (↑a : α) :=
  rfl
#align units.val_eq_coe Units.val_eq_coe
#align add_units.val_eq_coe AddUnits.val_eq_coe

#print Units.inv_eq_val_inv /-
@[simp, to_additive]
theorem inv_eq_val_inv : a.inv = ((a⁻¹ : αˣ) : α) :=
  rfl
#align units.inv_eq_coe_inv Units.inv_eq_val_inv
#align add_units.neg_eq_coe_neg AddUnits.neg_eq_val_neg
-/

#print Units.inv_mul /-
@[simp, to_additive]
theorem inv_mul : (↑a⁻¹ * a : α) = 1 :=
  inv_val _
#align units.inv_mul Units.inv_mul
#align add_units.neg_add AddUnits.neg_add
-/

#print Units.mul_inv /-
@[simp, to_additive]
theorem mul_inv : (a * ↑a⁻¹ : α) = 1 :=
  val_inv _
#align units.mul_inv Units.mul_inv
#align add_units.add_neg AddUnits.add_neg
-/

#print Units.inv_mul_of_eq /-
@[to_additive]
theorem inv_mul_of_eq {a : α} (h : ↑u = a) : ↑u⁻¹ * a = 1 := by rw [← h, u.inv_mul]
#align units.inv_mul_of_eq Units.inv_mul_of_eq
#align add_units.neg_add_of_eq AddUnits.neg_add_of_eq
-/

#print Units.mul_inv_of_eq /-
@[to_additive]
theorem mul_inv_of_eq {a : α} (h : ↑u = a) : a * ↑u⁻¹ = 1 := by rw [← h, u.mul_inv]
#align units.mul_inv_of_eq Units.mul_inv_of_eq
#align add_units.add_neg_of_eq AddUnits.add_neg_of_eq
-/

#print Units.mul_inv_cancel_left /-
@[simp, to_additive]
theorem mul_inv_cancel_left (a : αˣ) (b : α) : (a : α) * (↑a⁻¹ * b) = b := by
  rw [← mul_assoc, mul_inv, one_mul]
#align units.mul_inv_cancel_left Units.mul_inv_cancel_left
#align add_units.add_neg_cancel_left AddUnits.add_neg_cancel_left
-/

#print Units.inv_mul_cancel_left /-
@[simp, to_additive]
theorem inv_mul_cancel_left (a : αˣ) (b : α) : (↑a⁻¹ : α) * (a * b) = b := by
  rw [← mul_assoc, inv_mul, one_mul]
#align units.inv_mul_cancel_left Units.inv_mul_cancel_left
#align add_units.neg_add_cancel_left AddUnits.neg_add_cancel_left
-/

#print Units.mul_inv_cancel_right /-
@[simp, to_additive]
theorem mul_inv_cancel_right (a : α) (b : αˣ) : a * b * ↑b⁻¹ = a := by
  rw [mul_assoc, mul_inv, mul_one]
#align units.mul_inv_cancel_right Units.mul_inv_cancel_right
#align add_units.add_neg_cancel_right AddUnits.add_neg_cancel_right
-/

#print Units.inv_mul_cancel_right /-
@[simp, to_additive]
theorem inv_mul_cancel_right (a : α) (b : αˣ) : a * ↑b⁻¹ * b = a := by
  rw [mul_assoc, inv_mul, mul_one]
#align units.inv_mul_cancel_right Units.inv_mul_cancel_right
#align add_units.neg_add_cancel_right AddUnits.neg_add_cancel_right
-/

#print Units.mul_right_inj /-
@[simp, to_additive]
theorem mul_right_inj (a : αˣ) {b c : α} : (a : α) * b = a * c ↔ b = c :=
  ⟨fun h => by simpa only [inv_mul_cancel_left] using congr_arg ((· * ·) ↑(a⁻¹ : αˣ)) h,
    congr_arg _⟩
#align units.mul_right_inj Units.mul_right_inj
#align add_units.add_right_inj AddUnits.add_right_inj
-/

#print Units.mul_left_inj /-
@[simp, to_additive]
theorem mul_left_inj (a : αˣ) {b c : α} : b * a = c * a ↔ b = c :=
  ⟨fun h => by simpa only [mul_inv_cancel_right] using congr_arg (· * ↑(a⁻¹ : αˣ)) h, congr_arg _⟩
#align units.mul_left_inj Units.mul_left_inj
#align add_units.add_left_inj AddUnits.add_left_inj
-/

#print Units.eq_mul_inv_iff_mul_eq /-
@[to_additive]
theorem eq_mul_inv_iff_mul_eq {a b : α} : a = b * ↑c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩
#align units.eq_mul_inv_iff_mul_eq Units.eq_mul_inv_iff_mul_eq
#align add_units.eq_add_neg_iff_add_eq AddUnits.eq_add_neg_iff_add_eq
-/

#print Units.eq_inv_mul_iff_mul_eq /-
@[to_additive]
theorem eq_inv_mul_iff_mul_eq {a c : α} : a = ↑b⁻¹ * c ↔ ↑b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩
#align units.eq_inv_mul_iff_mul_eq Units.eq_inv_mul_iff_mul_eq
#align add_units.eq_neg_add_iff_add_eq AddUnits.eq_neg_add_iff_add_eq
-/

#print Units.inv_mul_eq_iff_eq_mul /-
@[to_additive]
theorem inv_mul_eq_iff_eq_mul {b c : α} : ↑a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩
#align units.inv_mul_eq_iff_eq_mul Units.inv_mul_eq_iff_eq_mul
#align add_units.neg_add_eq_iff_eq_add AddUnits.neg_add_eq_iff_eq_add
-/

#print Units.mul_inv_eq_iff_eq_mul /-
@[to_additive]
theorem mul_inv_eq_iff_eq_mul {a c : α} : a * ↑b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩
#align units.mul_inv_eq_iff_eq_mul Units.mul_inv_eq_iff_eq_mul
#align add_units.add_neg_eq_iff_eq_add AddUnits.add_neg_eq_iff_eq_add
-/

#print Units.inv_eq_of_mul_eq_one_left /-
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_left {a : α} (h : a * u = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = 1 * ↑u⁻¹ := by rw [one_mul]
    _ = a := by rw [← h, mul_inv_cancel_right]
#align units.inv_eq_of_mul_eq_one_left Units.inv_eq_of_mul_eq_one_left
#align add_units.neg_eq_of_add_eq_zero_left AddUnits.neg_eq_of_add_eq_zero_left
-/

#print Units.inv_eq_of_mul_eq_one_right /-
@[to_additive]
protected theorem inv_eq_of_mul_eq_one_right {a : α} (h : ↑u * a = 1) : ↑u⁻¹ = a :=
  calc
    ↑u⁻¹ = ↑u⁻¹ * 1 := by rw [mul_one]
    _ = a := by rw [← h, inv_mul_cancel_left]
#align units.inv_eq_of_mul_eq_one_right Units.inv_eq_of_mul_eq_one_right
#align add_units.neg_eq_of_add_eq_zero_right AddUnits.neg_eq_of_add_eq_zero_right
-/

#print Units.eq_inv_of_mul_eq_one_left /-
@[to_additive]
protected theorem eq_inv_of_mul_eq_one_left {a : α} (h : ↑u * a = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_right h).symm
#align units.eq_inv_of_mul_eq_one_left Units.eq_inv_of_mul_eq_one_left
#align add_units.eq_neg_of_add_eq_zero_left AddUnits.eq_neg_of_add_eq_zero_left
-/

#print Units.eq_inv_of_mul_eq_one_right /-
@[to_additive]
protected theorem eq_inv_of_mul_eq_one_right {a : α} (h : a * u = 1) : a = ↑u⁻¹ :=
  (Units.inv_eq_of_mul_eq_one_left h).symm
#align units.eq_inv_of_mul_eq_one_right Units.eq_inv_of_mul_eq_one_right
#align add_units.eq_neg_of_add_eq_zero_right AddUnits.eq_neg_of_add_eq_zero_right
-/

#print Units.mul_inv_eq_one /-
@[simp, to_additive]
theorem mul_inv_eq_one {a : α} : a * ↑u⁻¹ = 1 ↔ a = u :=
  ⟨inv_inv u ▸ Units.eq_inv_of_mul_eq_one_right, fun h => mul_inv_of_eq h.symm⟩
#align units.mul_inv_eq_one Units.mul_inv_eq_one
#align add_units.add_neg_eq_zero AddUnits.add_neg_eq_zero
-/

#print Units.inv_mul_eq_one /-
@[simp, to_additive]
theorem inv_mul_eq_one {a : α} : ↑u⁻¹ * a = 1 ↔ ↑u = a :=
  ⟨inv_inv u ▸ Units.inv_eq_of_mul_eq_one_right, inv_mul_of_eq⟩
#align units.inv_mul_eq_one Units.inv_mul_eq_one
#align add_units.neg_add_eq_zero AddUnits.neg_add_eq_zero
-/

#print Units.mul_eq_one_iff_eq_inv /-
@[to_additive]
theorem mul_eq_one_iff_eq_inv {a : α} : a * u = 1 ↔ a = ↑u⁻¹ := by rw [← mul_inv_eq_one, inv_inv]
#align units.mul_eq_one_iff_eq_inv Units.mul_eq_one_iff_eq_inv
#align add_units.add_eq_zero_iff_eq_neg AddUnits.add_eq_zero_iff_eq_neg
-/

#print Units.mul_eq_one_iff_inv_eq /-
@[to_additive]
theorem mul_eq_one_iff_inv_eq {a : α} : ↑u * a = 1 ↔ ↑u⁻¹ = a := by rw [← inv_mul_eq_one, inv_inv]
#align units.mul_eq_one_iff_inv_eq Units.mul_eq_one_iff_inv_eq
#align add_units.add_eq_zero_iff_neg_eq AddUnits.add_eq_zero_iff_neg_eq
-/

#print Units.inv_unique /-
@[to_additive]
theorem inv_unique {u₁ u₂ : αˣ} (h : (↑u₁ : α) = ↑u₂) : (↑u₁⁻¹ : α) = ↑u₂⁻¹ :=
  Units.inv_eq_of_mul_eq_one_right <| by rw [h, u₂.mul_inv]
#align units.inv_unique Units.inv_unique
#align add_units.neg_unique AddUnits.neg_unique
-/

#print Units.val_inv_eq_inv_val /-
@[simp, to_additive]
theorem val_inv_eq_inv_val {M : Type _} [DivisionMonoid M] (u : Units M) : ↑u⁻¹ = (u⁻¹ : M) :=
  Eq.symm <| inv_eq_of_mul_eq_one_right u.mul_inv
#align units.coe_inv Units.val_inv_eq_inv_val
#align add_units.coe_sub AddUnits.val_neg_eq_neg_val
-/

end Units

#print Units.mkOfMulEqOne /-
/-- For `a, b` in a `comm_monoid` such that `a * b = 1`, makes a unit out of `a`. -/
@[to_additive
      "For `a, b` in an `add_comm_monoid` such that `a + b = 0`, makes an add_unit\nout of `a`."]
def Units.mkOfMulEqOne [CommMonoid α] (a b : α) (hab : a * b = 1) : αˣ :=
  ⟨a, b, hab, (mul_comm b a).trans hab⟩
#align units.mk_of_mul_eq_one Units.mkOfMulEqOne
#align add_units.mk_of_add_eq_zero AddUnits.mkOfAddEqZero
-/

#print Units.val_mkOfMulEqOne /-
@[simp, to_additive]
theorem Units.val_mkOfMulEqOne [CommMonoid α] {a b : α} (h : a * b = 1) :
    (Units.mkOfMulEqOne a b h : α) = a :=
  rfl
#align units.coe_mk_of_mul_eq_one Units.val_mkOfMulEqOne
#align add_units.coe_mk_of_add_eq_zero AddUnits.val_mkOfAddEqZero
-/

section Monoid

variable [Monoid α] {a b c : α}

#print divp /-
/-- Partial division. It is defined when the
  second argument is invertible, and unlike the division operator
  in `division_ring` it is not totalized at zero. -/
def divp (a : α) (u) : α :=
  a * (u⁻¹ : αˣ)
#align divp divp
-/

infixl:70 " /ₚ " => divp

#print divp_self /-
@[simp]
theorem divp_self (u : αˣ) : (u : α) /ₚ u = 1 :=
  Units.mul_inv _
#align divp_self divp_self
-/

#print divp_one /-
@[simp]
theorem divp_one (a : α) : a /ₚ 1 = a :=
  mul_one _
#align divp_one divp_one
-/

#print divp_assoc /-
theorem divp_assoc (a b : α) (u : αˣ) : a * b /ₚ u = a * (b /ₚ u) :=
  mul_assoc _ _ _
#align divp_assoc divp_assoc
-/

#print divp_assoc' /-
/-- `field_simp` needs the reverse direction of `divp_assoc` to move all `/ₚ` to the right. -/
@[field_simps]
theorem divp_assoc' (x y : α) (u : αˣ) : x * (y /ₚ u) = x * y /ₚ u :=
  (divp_assoc _ _ _).symm
#align divp_assoc' divp_assoc'
-/

#print divp_inv /-
@[simp]
theorem divp_inv (u : αˣ) : a /ₚ u⁻¹ = a * u :=
  rfl
#align divp_inv divp_inv
-/

#print divp_mul_cancel /-
@[simp]
theorem divp_mul_cancel (a : α) (u : αˣ) : a /ₚ u * u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.inv_mul, mul_one]
#align divp_mul_cancel divp_mul_cancel
-/

#print mul_divp_cancel /-
@[simp]
theorem mul_divp_cancel (a : α) (u : αˣ) : a * u /ₚ u = a :=
  (mul_assoc _ _ _).trans <| by rw [Units.mul_inv, mul_one]
#align mul_divp_cancel mul_divp_cancel
-/

#print divp_left_inj /-
@[simp]
theorem divp_left_inj (u : αˣ) {a b : α} : a /ₚ u = b /ₚ u ↔ a = b :=
  Units.mul_left_inj _
#align divp_left_inj divp_left_inj
-/

#print divp_divp_eq_divp_mul /-
@[field_simps]
theorem divp_divp_eq_divp_mul (x : α) (u₁ u₂ : αˣ) : x /ₚ u₁ /ₚ u₂ = x /ₚ (u₂ * u₁) := by
  simp only [divp, mul_inv_rev, Units.val_mul, mul_assoc]
#align divp_divp_eq_divp_mul divp_divp_eq_divp_mul
-/

#print divp_eq_iff_mul_eq /-
@[field_simps]
theorem divp_eq_iff_mul_eq {x : α} {u : αˣ} {y : α} : x /ₚ u = y ↔ y * u = x :=
  u.mul_left_inj.symm.trans <| by rw [divp_mul_cancel] <;> exact ⟨Eq.symm, Eq.symm⟩
#align divp_eq_iff_mul_eq divp_eq_iff_mul_eq
-/

#print eq_divp_iff_mul_eq /-
@[field_simps]
theorem eq_divp_iff_mul_eq {x : α} {u : αˣ} {y : α} : x = y /ₚ u ↔ x * u = y := by
  rw [eq_comm, divp_eq_iff_mul_eq]
#align eq_divp_iff_mul_eq eq_divp_iff_mul_eq
-/

#print divp_eq_one_iff_eq /-
theorem divp_eq_one_iff_eq {a : α} {u : αˣ} : a /ₚ u = 1 ↔ a = u :=
  (Units.mul_left_inj u).symm.trans <| by rw [divp_mul_cancel, one_mul]
#align divp_eq_one_iff_eq divp_eq_one_iff_eq
-/

#print one_divp /-
@[simp]
theorem one_divp (u : αˣ) : 1 /ₚ u = ↑u⁻¹ :=
  one_mul _
#align one_divp one_divp
-/

#print inv_eq_one_divp /-
/-- Used for `field_simp` to deal with inverses of units. -/
@[field_simps]
theorem inv_eq_one_divp (u : αˣ) : ↑u⁻¹ = 1 /ₚ u := by rw [one_divp]
#align inv_eq_one_divp inv_eq_one_divp
-/

#print inv_eq_one_divp' /-
/-- Used for `field_simp` to deal with inverses of units. This form of the lemma
is essential since `field_simp` likes to use `inv_eq_one_div` to rewrite
`↑u⁻¹ = ↑(1 / u)`.
-/
@[field_simps]
theorem inv_eq_one_divp' (u : αˣ) : ((1 / u : αˣ) : α) = 1 /ₚ u := by rw [one_div, one_divp]
#align inv_eq_one_divp' inv_eq_one_divp'
-/

#print val_div_eq_divp /-
/-- `field_simp` moves division inside `αˣ` to the right, and this lemma
lifts the calculation to `α`.
-/
@[field_simps]
theorem val_div_eq_divp (u₁ u₂ : αˣ) : ↑(u₁ / u₂) = ↑u₁ /ₚ u₂ := by
  rw [divp, division_def, Units.val_mul]
#align coe_div_eq_divp val_div_eq_divp
-/

end Monoid

section CommMonoid

variable [CommMonoid α]

#print divp_mul_eq_mul_divp /-
@[field_simps]
theorem divp_mul_eq_mul_divp (x y : α) (u : αˣ) : x /ₚ u * y = x * y /ₚ u := by
  simp_rw [divp, mul_assoc, mul_comm]
#align divp_mul_eq_mul_divp divp_mul_eq_mul_divp
-/

#print divp_eq_divp_iff /-
-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_eq_divp_iff {x y : α} {ux uy : αˣ} : x /ₚ ux = y /ₚ uy ↔ x * uy = y * ux := by
  rw [divp_eq_iff_mul_eq, divp_mul_eq_mul_divp, divp_eq_iff_mul_eq]
#align divp_eq_divp_iff divp_eq_divp_iff
-/

#print divp_mul_divp /-
-- Theoretically redundant as `field_simp` lemma.
@[field_simps]
theorem divp_mul_divp (x y : α) (ux uy : αˣ) : x /ₚ ux * (y /ₚ uy) = x * y /ₚ (ux * uy) := by
  rw [divp_mul_eq_mul_divp, divp_assoc', divp_divp_eq_divp_mul]
#align divp_mul_divp divp_mul_divp
-/

variable [Subsingleton αˣ] {a b : α}

#print eq_one_of_mul_right /-
@[to_additive]
theorem eq_one_of_mul_right (h : a * b = 1) : a = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ (by rwa [mul_comm]) h) 1
#align eq_one_of_mul_right eq_one_of_mul_right
#align eq_zero_of_add_right eq_zero_of_add_right
-/

#print eq_one_of_mul_left /-
@[to_additive]
theorem eq_one_of_mul_left (h : a * b = 1) : b = 1 :=
  congr_arg Units.inv <| Subsingleton.elim (Units.mk _ _ h <| by rwa [mul_comm]) 1
#align eq_one_of_mul_left eq_one_of_mul_left
#align eq_zero_of_add_left eq_zero_of_add_left
-/

#print mul_eq_one /-
@[simp, to_additive]
theorem mul_eq_one : a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun h => ⟨eq_one_of_mul_right h, eq_one_of_mul_left h⟩, by rintro ⟨rfl, rfl⟩; exact mul_one _⟩
#align mul_eq_one mul_eq_one
#align add_eq_zero add_eq_zero
-/

end CommMonoid

/-!
# `is_unit` predicate

In this file we define the `is_unit` predicate on a `monoid`, and
prove a few basic properties. For the bundled version see `units`. See
also `prime`, `associated`, and `irreducible` in `algebra/associated`.

-/


section IsUnit

variable {M : Type _} {N : Type _}

#print IsUnit /-
/-- An element `a : M` of a monoid is a unit if it has a two-sided inverse.
The actual definition says that `a` is equal to some `u : Mˣ`, where
`Mˣ` is a bundled version of `is_unit`. -/
@[to_additive
      "An element `a : M` of an add_monoid is an `add_unit` if it has\na two-sided additive inverse. The actual definition says that `a` is equal to some\n`u : add_units M`, where `add_units M` is a bundled version of `is_add_unit`."]
def IsUnit [Monoid M] (a : M) : Prop :=
  ∃ u : Mˣ, (u : M) = a
#align is_unit IsUnit
#align is_add_unit IsAddUnit
-/

#print isUnit_of_subsingleton /-
@[nontriviality, to_additive]
theorem isUnit_of_subsingleton [Monoid M] [Subsingleton M] (a : M) : IsUnit a :=
  ⟨⟨a, a, Subsingleton.elim _ _, Subsingleton.elim _ _⟩, rfl⟩
#align is_unit_of_subsingleton isUnit_of_subsingleton
#align is_add_unit_of_subsingleton isAddUnit_of_subsingleton
-/

attribute [nontriviality] isAddUnit_of_subsingleton

@[to_additive]
instance [Monoid M] : CanLift M Mˣ coe IsUnit where prf _ := id

@[to_additive]
instance [Monoid M] [Subsingleton M] : Unique Mˣ
    where
  default := 1
  uniq a := Units.val_eq_one.mp <| Subsingleton.elim (a : M) 1

#print Units.isUnit /-
@[simp, to_additive is_add_unit_add_unit]
protected theorem Units.isUnit [Monoid M] (u : Mˣ) : IsUnit (u : M) :=
  ⟨u, rfl⟩
#align units.is_unit Units.isUnit
#align add_units.is_add_unit_add_unit AddUnits.isAddUnit
-/

#print isUnit_one /-
@[simp, to_additive]
theorem isUnit_one [Monoid M] : IsUnit (1 : M) :=
  ⟨1, rfl⟩
#align is_unit_one isUnit_one
#align is_add_unit_zero isAddUnit_zero
-/

#print isUnit_of_mul_eq_one /-
@[to_additive]
theorem isUnit_of_mul_eq_one [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨Units.mkOfMulEqOne a b h, rfl⟩
#align is_unit_of_mul_eq_one isUnit_of_mul_eq_one
#align is_add_unit_of_add_eq_zero isAddUnit_of_add_eq_zero
-/

#print IsUnit.exists_right_inv /-
@[to_additive IsAddUnit.exists_neg]
theorem IsUnit.exists_right_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, a * b = 1 := by
  rcases h with ⟨⟨a, b, hab, _⟩, rfl⟩; exact ⟨b, hab⟩
#align is_unit.exists_right_inv IsUnit.exists_right_inv
#align is_add_unit.exists_neg IsAddUnit.exists_neg
-/

#print IsUnit.exists_left_inv /-
@[to_additive IsAddUnit.exists_neg']
theorem IsUnit.exists_left_inv [Monoid M] {a : M} (h : IsUnit a) : ∃ b, b * a = 1 := by
  rcases h with ⟨⟨a, b, _, hba⟩, rfl⟩; exact ⟨b, hba⟩
#align is_unit.exists_left_inv IsUnit.exists_left_inv
#align is_add_unit.exists_neg' IsAddUnit.exists_neg'
-/

#print isUnit_iff_exists_inv /-
@[to_additive]
theorem isUnit_iff_exists_inv [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, a * b = 1 :=
  ⟨fun h => h.exists_right_inv, fun ⟨b, hab⟩ => isUnit_of_mul_eq_one _ b hab⟩
#align is_unit_iff_exists_inv isUnit_iff_exists_inv
#align is_add_unit_iff_exists_neg isAddUnit_iff_exists_neg
-/

#print isUnit_iff_exists_inv' /-
@[to_additive]
theorem isUnit_iff_exists_inv' [CommMonoid M] {a : M} : IsUnit a ↔ ∃ b, b * a = 1 := by
  simp [isUnit_iff_exists_inv, mul_comm]
#align is_unit_iff_exists_inv' isUnit_iff_exists_inv'
#align is_add_unit_iff_exists_neg' isAddUnit_iff_exists_neg'
-/

#print IsUnit.mul /-
@[to_additive]
theorem IsUnit.mul [Monoid M] {x y : M} : IsUnit x → IsUnit y → IsUnit (x * y) := by
  rintro ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x * y, Units.val_mul _ _⟩
#align is_unit.mul IsUnit.mul
#align is_add_unit.add IsAddUnit.add
-/

#print Units.isUnit_mul_units /-
/-- Multiplication by a `u : Mˣ` on the right doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the right doesn't\naffect `is_add_unit`."]
theorem Units.isUnit_mul_units [Monoid M] (a : M) (u : Mˣ) : IsUnit (a * u) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ =>
      by
      have : IsUnit (a * ↑u * ↑u⁻¹) := by exists v * u⁻¹ <;> rw [← hv, Units.val_mul]
      rwa [mul_assoc, Units.mul_inv, mul_one] at this )
    fun v => v.mul u.IsUnit
#align units.is_unit_mul_units Units.isUnit_mul_units
#align add_units.is_add_unit_add_add_units AddUnits.isAddUnit_add_addUnits
-/

#print Units.isUnit_units_mul /-
/-- Multiplication by a `u : Mˣ` on the left doesn't affect `is_unit`. -/
@[simp, to_additive "Addition of a `u : add_units M` on the left doesn't affect `is_add_unit`."]
theorem Units.isUnit_units_mul {M : Type _} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u * a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ =>
      by
      have : IsUnit (↑u⁻¹ * (↑u * a)) := by exists u⁻¹ * v <;> rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this )
    u.IsUnit.mul
#align units.is_unit_units_mul Units.isUnit_units_mul
#align add_units.is_add_unit_add_units_add AddUnits.isAddUnit_addUnits_add
-/

#print isUnit_of_mul_isUnit_left /-
@[to_additive]
theorem isUnit_of_mul_isUnit_left [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x :=
  let ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hu
  isUnit_iff_exists_inv.2 ⟨y * z, by rwa [← mul_assoc]⟩
#align is_unit_of_mul_is_unit_left isUnit_of_mul_isUnit_left
#align is_add_unit_of_add_is_add_unit_left isAddUnit_of_add_isAddUnit_left
-/

#print isUnit_of_mul_isUnit_right /-
@[to_additive]
theorem isUnit_of_mul_isUnit_right [CommMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y :=
  @isUnit_of_mul_isUnit_left _ _ y x <| by rwa [mul_comm]
#align is_unit_of_mul_is_unit_right isUnit_of_mul_isUnit_right
#align is_add_unit_of_add_is_add_unit_right isAddUnit_of_add_isAddUnit_right
-/

namespace IsUnit

#print IsUnit.mul_iff /-
@[simp, to_additive]
theorem mul_iff [CommMonoid M] {x y : M} : IsUnit (x * y) ↔ IsUnit x ∧ IsUnit y :=
  ⟨fun h => ⟨isUnit_of_mul_isUnit_left h, isUnit_of_mul_isUnit_right h⟩, fun h =>
    IsUnit.mul h.1 h.2⟩
#align is_unit.mul_iff IsUnit.mul_iff
#align is_add_unit.add_iff IsAddUnit.add_iff
-/

section Monoid

variable [Monoid M] {a b c : M}

#print IsUnit.unit /-
/-- The element of the group of units, corresponding to an element of a monoid which is a unit. When
`α` is a `division_monoid`, use `is_unit.unit'` instead. -/
@[to_additive
      "The element of the additive group of additive units, corresponding to an element of\nan additive monoid which is an additive unit. When `α` is a `subtraction_monoid`, use\n`is_add_unit.add_unit'` instead."]
protected noncomputable def unit (h : IsUnit a) : Mˣ :=
  (Classical.choose h).copy a (Classical.choose_spec h).symm _ rfl
#align is_unit.unit IsUnit.unit
#align is_add_unit.add_unit IsAddUnit.addUnit
-/

#print IsUnit.unit_of_val_units /-
@[simp, to_additive]
theorem unit_of_val_units {a : Mˣ} (h : IsUnit (a : M)) : h.Unit = a :=
  Units.ext <| rfl
#align is_unit.unit_of_coe_units IsUnit.unit_of_val_units
#align is_add_unit.add_unit_of_coe_add_units IsAddUnit.addUnit_of_val_addUnits
-/

#print IsUnit.unit_spec /-
@[simp, to_additive]
theorem unit_spec (h : IsUnit a) : ↑h.Unit = a :=
  rfl
#align is_unit.unit_spec IsUnit.unit_spec
#align is_add_unit.add_unit_spec IsAddUnit.addUnit_spec
-/

#print IsUnit.val_inv_mul /-
@[simp, to_additive]
theorem val_inv_mul (h : IsUnit a) : ↑h.Unit⁻¹ * a = 1 :=
  Units.mul_inv _
#align is_unit.coe_inv_mul IsUnit.val_inv_mul
#align is_add_unit.coe_neg_add IsAddUnit.val_neg_add
-/

#print IsUnit.mul_val_inv /-
@[simp, to_additive]
theorem mul_val_inv (h : IsUnit a) : a * ↑h.Unit⁻¹ = 1 := by convert h.unit.mul_inv
#align is_unit.mul_coe_inv IsUnit.mul_val_inv
#align is_add_unit.add_coe_neg IsAddUnit.add_val_neg
-/

/-- `is_unit x` is decidable if we can decide if `x` comes from `Mˣ`. -/
@[to_additive "`is_add_unit x` is decidable if we can decide if `x` comes from `add_units M"]
instance (x : M) [h : Decidable (∃ u : Mˣ, ↑u = x)] : Decidable (IsUnit x) :=
  h

#print IsUnit.mul_left_inj /-
@[to_additive]
theorem mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_left_inj
#align is_unit.mul_left_inj IsUnit.mul_left_inj
#align is_add_unit.add_left_inj IsAddUnit.add_left_inj
-/

#print IsUnit.mul_right_inj /-
@[to_additive]
theorem mul_right_inj (h : IsUnit a) : a * b = a * c ↔ b = c :=
  let ⟨u, hu⟩ := h
  hu ▸ u.mul_right_inj
#align is_unit.mul_right_inj IsUnit.mul_right_inj
#align is_add_unit.add_right_inj IsAddUnit.add_right_inj
-/

#print IsUnit.mul_left_cancel /-
@[to_additive]
protected theorem mul_left_cancel (h : IsUnit a) : a * b = a * c → b = c :=
  h.mul_right_inj.1
#align is_unit.mul_left_cancel IsUnit.mul_left_cancel
#align is_add_unit.add_left_cancel IsAddUnit.add_left_cancel
-/

#print IsUnit.mul_right_cancel /-
@[to_additive]
protected theorem mul_right_cancel (h : IsUnit b) : a * b = c * b → a = c :=
  h.mul_left_inj.1
#align is_unit.mul_right_cancel IsUnit.mul_right_cancel
#align is_add_unit.add_right_cancel IsAddUnit.add_right_cancel
-/

#print IsUnit.mul_right_injective /-
@[to_additive]
protected theorem mul_right_injective (h : IsUnit a) : Injective ((· * ·) a) := fun _ _ =>
  h.hMul_left_cancel
#align is_unit.mul_right_injective IsUnit.mul_right_injective
#align is_add_unit.add_right_injective IsAddUnit.add_right_injective
-/

#print IsUnit.mul_left_injective /-
@[to_additive]
protected theorem mul_left_injective (h : IsUnit b) : Injective (· * b) := fun _ _ =>
  h.hMul_right_cancel
#align is_unit.mul_left_injective IsUnit.mul_left_injective
#align is_add_unit.add_left_injective IsAddUnit.add_left_injective
-/

end Monoid

variable [DivisionMonoid M] {a : M}

#print IsUnit.inv_mul_cancel /-
@[simp, to_additive]
protected theorem inv_mul_cancel : IsUnit a → a⁻¹ * a = 1 := by rintro ⟨u, rfl⟩;
  rw [← Units.val_inv_eq_inv_val, Units.inv_mul]
#align is_unit.inv_mul_cancel IsUnit.inv_mul_cancel
#align is_add_unit.neg_add_cancel IsAddUnit.neg_add_cancel
-/

#print IsUnit.mul_inv_cancel /-
@[simp, to_additive]
protected theorem mul_inv_cancel : IsUnit a → a * a⁻¹ = 1 := by rintro ⟨u, rfl⟩;
  rw [← Units.val_inv_eq_inv_val, Units.mul_inv]
#align is_unit.mul_inv_cancel IsUnit.mul_inv_cancel
#align is_add_unit.add_neg_cancel IsAddUnit.add_neg_cancel
-/

end IsUnit

-- namespace
end IsUnit

-- section
section NoncomputableDefs

variable {M : Type _}

#print groupOfIsUnit /-
/-- Constructs a `group` structure on a `monoid` consisting only of units. -/
noncomputable def groupOfIsUnit [hM : Monoid M] (h : ∀ a : M, IsUnit a) : Group M :=
  { hM with
    inv := fun a => ↑(h a).Unit⁻¹
    hMul_left_inv := fun a => by
      change ↑(h a).Unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align group_of_is_unit groupOfIsUnit
-/

#print commGroupOfIsUnit /-
/-- Constructs a `comm_group` structure on a `comm_monoid` consisting only of units. -/
noncomputable def commGroupOfIsUnit [hM : CommMonoid M] (h : ∀ a : M, IsUnit a) : CommGroup M :=
  { hM with
    inv := fun a => ↑(h a).Unit⁻¹
    hMul_left_inv := fun a => by
      change ↑(h a).Unit⁻¹ * a = 1
      rw [Units.inv_mul_eq_iff_eq_mul, (h a).unit_spec, mul_one] }
#align comm_group_of_is_unit commGroupOfIsUnit
-/

end NoncomputableDefs

