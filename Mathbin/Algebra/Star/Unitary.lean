/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shing Tak Lam, Frédéric Dupuis
-/
import Algebra.Star.Basic
import Algebra.Group.Submonoid.Operations

#align_import algebra.star.unitary from "leanprover-community/mathlib"@"be24ec5de6701447e5df5ca75400ffee19d65659"

/-!
# Unitary elements of a star monoid

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `unitary R`, where `R` is a star monoid, as the submonoid made of the elements
that satisfy `star U * U = 1` and `U * star U = 1`, and these form a group.
This includes, for instance, unitary operators on Hilbert spaces.

See also `matrix.unitary_group` for specializations to `unitary (matrix n n R)`.

## Tags

unitary
-/


#print unitary /-
/-- In a *-monoid, `unitary R` is the submonoid consisting of all the elements `U` of
`R` such that `star U * U = 1` and `U * star U = 1`.
-/
def unitary (R : Type _) [Monoid R] [StarMul R] : Submonoid R
    where
  carrier := {U | star U * U = 1 ∧ U * star U = 1}
  one_mem' := by simp only [mul_one, and_self_iff, Set.mem_setOf_eq, star_one]
  hMul_mem' := fun U B ⟨hA₁, hA₂⟩ ⟨hB₁, hB₂⟩ =>
    by
    refine' ⟨_, _⟩
    ·
      calc
        star (U * B) * (U * B) = star B * star U * U * B := by simp only [mul_assoc, star_mul]
        _ = star B * (star U * U) * B := by rw [← mul_assoc]
        _ = 1 := by rw [hA₁, mul_one, hB₁]
    ·
      calc
        U * B * star (U * B) = U * B * (star B * star U) := by rw [star_mul]
        _ = U * (B * star B) * star U := by simp_rw [← mul_assoc]
        _ = 1 := by rw [hB₂, mul_one, hA₂]
#align unitary unitary
-/

variable {R : Type _}

namespace unitary

section Monoid

variable [Monoid R] [StarMul R]

#print unitary.mem_iff /-
theorem mem_iff {U : R} : U ∈ unitary R ↔ star U * U = 1 ∧ U * star U = 1 :=
  Iff.rfl
#align unitary.mem_iff unitary.mem_iff
-/

#print unitary.star_mul_self_of_mem /-
@[simp]
theorem star_mul_self_of_mem {U : R} (hU : U ∈ unitary R) : star U * U = 1 :=
  hU.1
#align unitary.star_mul_self_of_mem unitary.star_mul_self_of_mem
-/

#print unitary.mul_star_self_of_mem /-
@[simp]
theorem mul_star_self_of_mem {U : R} (hU : U ∈ unitary R) : U * star U = 1 :=
  hU.2
#align unitary.mul_star_self_of_mem unitary.mul_star_self_of_mem
-/

#print unitary.star_mem /-
theorem star_mem {U : R} (hU : U ∈ unitary R) : star U ∈ unitary R :=
  ⟨by rw [star_star, mul_star_self_of_mem hU], by rw [star_star, star_mul_self_of_mem hU]⟩
#align unitary.star_mem unitary.star_mem
-/

#print unitary.star_mem_iff /-
@[simp]
theorem star_mem_iff {U : R} : star U ∈ unitary R ↔ U ∈ unitary R :=
  ⟨fun h => star_star U ▸ star_mem h, star_mem⟩
#align unitary.star_mem_iff unitary.star_mem_iff
-/

instance : Star (unitary R) :=
  ⟨fun U => ⟨star U, star_mem U.IProp⟩⟩

#print unitary.coe_star /-
@[simp, norm_cast]
theorem coe_star {U : unitary R} : ↑(star U) = (star U : R) :=
  rfl
#align unitary.coe_star unitary.coe_star
-/

#print unitary.coe_star_mul_self /-
theorem coe_star_mul_self (U : unitary R) : (star U : R) * U = 1 :=
  star_mul_self_of_mem U.IProp
#align unitary.coe_star_mul_self unitary.coe_star_mul_self
-/

#print unitary.coe_mul_star_self /-
theorem coe_mul_star_self (U : unitary R) : (U : R) * star U = 1 :=
  mul_star_self_of_mem U.IProp
#align unitary.coe_mul_star_self unitary.coe_mul_star_self
-/

#print unitary.star_mul_self /-
@[simp]
theorem star_mul_self (U : unitary R) : star U * U = 1 :=
  Subtype.ext <| coe_star_mul_self U
#align unitary.star_mul_self unitary.star_mul_self
-/

#print unitary.mul_star_self /-
@[simp]
theorem mul_star_self (U : unitary R) : U * star U = 1 :=
  Subtype.ext <| coe_mul_star_self U
#align unitary.mul_star_self unitary.mul_star_self
-/

instance : Group (unitary R) :=
  { Submonoid.toMonoid _ with
    inv := star
    hMul_left_inv := star_mul_self }

instance : InvolutiveStar (unitary R) :=
  ⟨fun _ => by ext; simp only [coe_star, star_star]⟩

instance : StarMul (unitary R) :=
  ⟨fun _ _ => by ext; simp only [coe_star, Submonoid.coe_mul, star_mul]⟩

instance : Inhabited (unitary R) :=
  ⟨1⟩

#print unitary.star_eq_inv /-
theorem star_eq_inv (U : unitary R) : star U = U⁻¹ :=
  rfl
#align unitary.star_eq_inv unitary.star_eq_inv
-/

#print unitary.star_eq_inv' /-
theorem star_eq_inv' : (star : unitary R → unitary R) = Inv.inv :=
  rfl
#align unitary.star_eq_inv' unitary.star_eq_inv'
-/

#print unitary.toUnits /-
/-- The unitary elements embed into the units. -/
@[simps]
def toUnits : unitary R →* Rˣ
    where
  toFun x := ⟨x, ↑x⁻¹, coe_mul_star_self x, coe_star_mul_self x⟩
  map_one' := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align unitary.to_units unitary.toUnits
-/

#print unitary.toUnits_injective /-
theorem toUnits_injective : Function.Injective (toUnits : unitary R → Rˣ) := fun x y h =>
  Subtype.ext <| Units.ext_iff.mp h
#align unitary.to_units_injective unitary.toUnits_injective
-/

end Monoid

section CommMonoid

variable [CommMonoid R] [StarMul R]

instance : CommGroup (unitary R) :=
  { unitary.group, Submonoid.toCommMonoid _ with }

#print unitary.mem_iff_star_mul_self /-
theorem mem_iff_star_mul_self {U : R} : U ∈ unitary R ↔ star U * U = 1 :=
  mem_iff.trans <| and_iff_left_of_imp fun h => mul_comm (star U) U ▸ h
#align unitary.mem_iff_star_mul_self unitary.mem_iff_star_mul_self
-/

#print unitary.mem_iff_self_mul_star /-
theorem mem_iff_self_mul_star {U : R} : U ∈ unitary R ↔ U * star U = 1 :=
  mem_iff.trans <| and_iff_right_of_imp fun h => mul_comm U (star U) ▸ h
#align unitary.mem_iff_self_mul_star unitary.mem_iff_self_mul_star
-/

end CommMonoid

section GroupWithZero

variable [GroupWithZero R] [StarMul R]

#print unitary.coe_inv /-
@[norm_cast]
theorem coe_inv (U : unitary R) : ↑U⁻¹ = (U⁻¹ : R) :=
  eq_inv_of_mul_eq_one_right <| coe_mul_star_self _
#align unitary.coe_inv unitary.coe_inv
-/

#print unitary.coe_div /-
@[norm_cast]
theorem coe_div (U₁ U₂ : unitary R) : ↑(U₁ / U₂) = (U₁ / U₂ : R) := by
  simp only [div_eq_mul_inv, coe_inv, Submonoid.coe_mul]
#align unitary.coe_div unitary.coe_div
-/

#print unitary.coe_zpow /-
@[norm_cast]
theorem coe_zpow (U : unitary R) (z : ℤ) : ↑(U ^ z) = (U ^ z : R) :=
  by
  induction z
  · simp [SubmonoidClass.coe_pow]
  · simp [coe_inv]
#align unitary.coe_zpow unitary.coe_zpow
-/

end GroupWithZero

section Ring

variable [Ring R] [StarRing R]

instance : Neg (unitary R)
    where neg U := ⟨-U, by simp_rw [mem_iff, star_neg, neg_mul_neg]; exact U.prop⟩

#print unitary.coe_neg /-
@[norm_cast]
theorem coe_neg (U : unitary R) : ↑(-U) = (-U : R) :=
  rfl
#align unitary.coe_neg unitary.coe_neg
-/

instance : HasDistribNeg (unitary R) :=
  Subtype.coe_injective.HasDistribNeg _ coe_neg (unitary R).val_mul

end Ring

end unitary

