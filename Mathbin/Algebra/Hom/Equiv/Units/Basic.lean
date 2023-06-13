/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.hom.equiv.units.basic
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Hom.Units

/-!
# Multiplicative and additive equivalence acting on units.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {F α β A B M N P Q G H : Type _}

#print toUnits /-
/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ
    where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun := coe
  left_inv x := rfl
  right_inv u := Units.ext rfl
  map_mul' x y := Units.ext rfl
#align to_units toUnits
#align to_add_units toAddUnits
-/

#print coe_toUnits /-
@[simp, to_additive]
theorem coe_toUnits [Group G] (g : G) : (toUnits g : G) = g :=
  rfl
#align coe_to_units coe_toUnits
#align coe_to_add_units coe_toAddUnits
-/

namespace Units

variable [Monoid M] [Monoid N] [Monoid P]

#print Units.mapEquiv /-
/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with
    invFun := map h.symm.toMonoidHom
    left_inv := fun u => ext <| h.left_inv u
    right_inv := fun u => ext <| h.right_inv u }
#align units.map_equiv Units.mapEquiv
-/

#print Units.mapEquiv_symm /-
@[simp]
theorem mapEquiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl
#align units.map_equiv_symm Units.mapEquiv_symm
-/

#print Units.coe_mapEquiv /-
@[simp]
theorem coe_mapEquiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl
#align units.coe_map_equiv Units.coe_mapEquiv
-/

#print Units.mulLeft /-
/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := ↑u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left
#align units.mul_left Units.mulLeft
#align add_units.add_left AddUnits.addLeft
-/

#print Units.mulLeft_symm /-
@[simp, to_additive]
theorem mulLeft_symm (u : Mˣ) : u.mulLeft.symm = u⁻¹.mulLeft :=
  Equiv.ext fun x => rfl
#align units.mul_left_symm Units.mulLeft_symm
#align add_units.add_left_symm AddUnits.addLeft_symm
-/

#print Units.mulLeft_bijective /-
@[to_additive]
theorem mulLeft_bijective (a : Mˣ) : Function.Bijective ((· * ·) a : M → M) :=
  (mulLeft a).Bijective
#align units.mul_left_bijective Units.mulLeft_bijective
#align add_units.add_left_bijective AddUnits.addLeft_bijective
-/

#print Units.mulRight /-
/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u
#align units.mul_right Units.mulRight
#align add_units.add_right AddUnits.addRight
-/

#print Units.mulRight_symm /-
@[simp, to_additive]
theorem mulRight_symm (u : Mˣ) : u.mulRight.symm = u⁻¹.mulRight :=
  Equiv.ext fun x => rfl
#align units.mul_right_symm Units.mulRight_symm
#align add_units.add_right_symm AddUnits.addRight_symm
-/

#print Units.mulRight_bijective /-
@[to_additive]
theorem mulRight_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).Bijective
#align units.mul_right_bijective Units.mulRight_bijective
#align add_units.add_right_bijective AddUnits.addRight_bijective
-/

end Units

namespace Equiv

section Group

variable [Group G]

#print Equiv.mulLeft /-
/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mulLeft
#align equiv.mul_left Equiv.mulLeft
#align equiv.add_left Equiv.addLeft
-/

#print Equiv.coe_mulLeft /-
@[simp, to_additive]
theorem coe_mulLeft (a : G) : ⇑(Equiv.mulLeft a) = (· * ·) a :=
  rfl
#align equiv.coe_mul_left Equiv.coe_mulLeft
#align equiv.coe_add_left Equiv.coe_addLeft
-/

#print Equiv.mulLeft_symm_apply /-
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulLeft_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (· * ·) a⁻¹ :=
  rfl
#align equiv.mul_left_symm_apply Equiv.mulLeft_symm_apply
#align equiv.add_left_symm_apply Equiv.addLeft_symm_apply
-/

#print Equiv.mulLeft_symm /-
@[simp, to_additive]
theorem mulLeft_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun x => rfl
#align equiv.mul_left_symm Equiv.mulLeft_symm
#align equiv.add_left_symm Equiv.addLeft_symm
-/

#print Group.mulLeft_bijective /-
@[to_additive]
theorem Group.mulLeft_bijective (a : G) : Function.Bijective ((· * ·) a) :=
  (Equiv.mulLeft a).Bijective
#align group.mul_left_bijective Group.mulLeft_bijective
#align add_group.add_left_bijective AddGroup.addLeft_bijective
-/

#print Equiv.mulRight /-
/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mulRight
#align equiv.mul_right Equiv.mulRight
#align equiv.add_right Equiv.addRight
-/

#print Equiv.coe_mulRight /-
@[simp, to_additive]
theorem coe_mulRight (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl
#align equiv.coe_mul_right Equiv.coe_mulRight
#align equiv.coe_add_right Equiv.coe_addRight
-/

#print Equiv.mulRight_symm /-
@[simp, to_additive]
theorem mulRight_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun x => rfl
#align equiv.mul_right_symm Equiv.mulRight_symm
#align equiv.add_right_symm Equiv.addRight_symm
-/

#print Equiv.mulRight_symm_apply /-
/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf,
  to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mulRight_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl
#align equiv.mul_right_symm_apply Equiv.mulRight_symm_apply
#align equiv.add_right_symm_apply Equiv.addRight_symm_apply
-/

#print Group.mulRight_bijective /-
@[to_additive]
theorem Group.mulRight_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).Bijective
#align group.mul_right_bijective Group.mulRight_bijective
#align add_group.add_right_bijective AddGroup.addRight_bijective
-/

#print Equiv.divLeft /-
/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `equiv.add_left a (-b)` that is defeq to `a - b`. ", simps]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_left Equiv.divLeft
#align equiv.sub_left Equiv.subLeft
-/

#print Equiv.divLeft_eq_inv_trans_mulLeft /-
@[to_additive]
theorem divLeft_eq_inv_trans_mulLeft (a : G) :
    Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_left_eq_inv_trans_mul_left Equiv.divLeft_eq_inv_trans_mulLeft
#align equiv.sub_left_eq_neg_trans_add_left Equiv.subLeft_eq_neg_trans_addLeft
-/

#print Equiv.divRight /-
/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `equiv.add_right (-a) b` that is defeq to `b - a`. ", simps]
protected def divRight (a : G) : G ≃ G
    where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]
#align equiv.div_right Equiv.divRight
#align equiv.sub_right Equiv.subRight
-/

#print Equiv.divRight_eq_mulRight_inv /-
@[to_additive]
theorem divRight_eq_mulRight_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _
#align equiv.div_right_eq_mul_right_inv Equiv.divRight_eq_mulRight_inv
#align equiv.sub_right_eq_add_right_neg Equiv.subRight_eq_addRight_neg
-/

end Group

end Equiv

#print MulEquiv.inv /-
/-- In a `division_comm_monoid`, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`.", simps apply]
def MulEquiv.inv (G : Type _) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with
    toFun := Inv.inv
    invFun := Inv.inv
    map_mul' := mul_inv }
#align mul_equiv.inv MulEquiv.inv
#align add_equiv.neg AddEquiv.neg
-/

#print MulEquiv.inv_symm /-
@[simp]
theorem MulEquiv.inv_symm (G : Type _) [DivisionCommMonoid G] :
    (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl
#align mul_equiv.inv_symm MulEquiv.inv_symm
-/

