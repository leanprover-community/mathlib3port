/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.GroupWithZero.Units

/-!
# Multiplicative and additive equivalence acting on units.
-/


variable {F α β A B M N P Q G H : Type _}

/-- A group is isomorphic to its group of units. -/
@[to_additive "An additive group is isomorphic to its group of additive units"]
def toUnits [Group G] : G ≃* Gˣ where
  toFun x := ⟨x, x⁻¹, mul_inv_self _, inv_mul_self _⟩
  invFun := coe
  left_inv x := rfl
  right_inv u := Units.ext rfl
  map_mul' x y := Units.ext rfl

@[simp, to_additive]
theorem coe_to_units [Group G] (g : G) : (toUnits g : G) = g :=
  rfl

namespace Units

variable [Monoid M] [Monoid N] [Monoid P]

/-- A multiplicative equivalence of monoids defines a multiplicative equivalence
of their groups of units. -/
def mapEquiv (h : M ≃* N) : Mˣ ≃* Nˣ :=
  { map h.toMonoidHom with invFun := map h.symm.toMonoidHom, left_inv := fun u => ext <| h.left_inv u,
    right_inv := fun u => ext <| h.right_inv u }

@[simp]
theorem map_equiv_symm (h : M ≃* N) : (mapEquiv h).symm = mapEquiv h.symm :=
  rfl

@[simp]
theorem coe_map_equiv (h : M ≃* N) (x : Mˣ) : (mapEquiv h x : N) = h x :=
  rfl

/-- Left multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Left addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulLeft (u : Mˣ) : Equiv.Perm M where
  toFun x := u * x
  invFun x := ↑u⁻¹ * x
  left_inv := u.inv_mul_cancel_left
  right_inv := u.mul_inv_cancel_left

@[simp, to_additive]
theorem mul_left_symm (u : Mˣ) : u.mul_left.symm = u⁻¹.mul_left :=
  Equiv.ext fun x => rfl

@[to_additive]
theorem mul_left_bijective (a : Mˣ) : Function.Bijective ((· * ·) a : M → M) :=
  (mulLeft a).Bijective

/-- Right multiplication by a unit of a monoid is a permutation of the underlying type. -/
@[to_additive "Right addition of an additive unit is a permutation of the underlying type.",
  simps (config := { fullyApplied := false }) apply]
def mulRight (u : Mˣ) : Equiv.Perm M where
  toFun x := x * u
  invFun x := x * ↑u⁻¹
  left_inv x := mul_inv_cancel_right x u
  right_inv x := inv_mul_cancel_right x u

@[simp, to_additive]
theorem mul_right_symm (u : Mˣ) : u.mul_right.symm = u⁻¹.mul_right :=
  Equiv.ext fun x => rfl

@[to_additive]
theorem mul_right_bijective (a : Mˣ) : Function.Bijective ((· * a) : M → M) :=
  (mulRight a).Bijective

end Units

namespace Equiv

section Group

variable [Group G]

/-- Left multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Left addition in an `add_group` is a permutation of the underlying type."]
protected def mulLeft (a : G) : Perm G :=
  (toUnits a).mul_left

@[simp, to_additive]
theorem coe_mul_left (a : G) : ⇑(Equiv.mulLeft a) = (· * ·) a :=
  rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mul_left_symm_apply (a : G) : ((Equiv.mulLeft a).symm : G → G) = (· * ·) a⁻¹ :=
  rfl

@[simp, to_additive]
theorem mul_left_symm (a : G) : (Equiv.mulLeft a).symm = Equiv.mulLeft a⁻¹ :=
  ext fun x => rfl

@[to_additive]
theorem _root_.group.mul_left_bijective (a : G) : Function.Bijective ((· * ·) a) :=
  (Equiv.mulLeft a).Bijective

/-- Right multiplication in a `group` is a permutation of the underlying type. -/
@[to_additive "Right addition in an `add_group` is a permutation of the underlying type."]
protected def mulRight (a : G) : Perm G :=
  (toUnits a).mul_right

@[simp, to_additive]
theorem coe_mul_right (a : G) : ⇑(Equiv.mulRight a) = fun x => x * a :=
  rfl

@[simp, to_additive]
theorem mul_right_symm (a : G) : (Equiv.mulRight a).symm = Equiv.mulRight a⁻¹ :=
  ext fun x => rfl

/-- Extra simp lemma that `dsimp` can use. `simp` will never use this. -/
@[simp, nolint simp_nf, to_additive "Extra simp lemma that `dsimp` can use. `simp` will never use this."]
theorem mul_right_symm_apply (a : G) : ((Equiv.mulRight a).symm : G → G) = fun x => x * a⁻¹ :=
  rfl

@[to_additive]
theorem _root_.group.mul_right_bijective (a : G) : Function.Bijective (· * a) :=
  (Equiv.mulRight a).Bijective

/-- A version of `equiv.mul_left a b⁻¹` that is defeq to `a / b`. -/
@[to_additive " A version of `equiv.add_left a (-b)` that is defeq to `a - b`. ", simps]
protected def divLeft (a : G) : G ≃ G where
  toFun b := a / b
  invFun b := b⁻¹ * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem div_left_eq_inv_trans_mul_left (a : G) : Equiv.divLeft a = (Equiv.inv G).trans (Equiv.mulLeft a) :=
  ext fun _ => div_eq_mul_inv _ _

/-- A version of `equiv.mul_right a⁻¹ b` that is defeq to `b / a`. -/
@[to_additive " A version of `equiv.add_right (-a) b` that is defeq to `b - a`. ", simps]
protected def divRight (a : G) : G ≃ G where
  toFun b := b / a
  invFun b := b * a
  left_inv b := by simp [div_eq_mul_inv]
  right_inv b := by simp [div_eq_mul_inv]

@[to_additive]
theorem div_right_eq_mul_right_inv (a : G) : Equiv.divRight a = Equiv.mulRight a⁻¹ :=
  ext fun _ => div_eq_mul_inv _ _

end Group

section GroupWithZero

variable [GroupWithZero G]

/-- Left multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulLeft₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mul_left

theorem _root_.mul_left_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * ·) a : G → G) :=
  (Equiv.mulLeft₀ a ha).Bijective

/-- Right multiplication by a nonzero element in a `group_with_zero` is a permutation of the
underlying type. -/
@[simps (config := { fullyApplied := false })]
protected def mulRight₀ (a : G) (ha : a ≠ 0) : Perm G :=
  (Units.mk0 a ha).mul_right

theorem _root_.mul_right_bijective₀ (a : G) (ha : a ≠ 0) : Function.Bijective ((· * a) : G → G) :=
  (Equiv.mulRight₀ a ha).Bijective

end GroupWithZero

end Equiv

/-- In a `division_comm_monoid`, `equiv.inv` is a `mul_equiv`. There is a variant of this
`mul_equiv.inv' G : G ≃* Gᵐᵒᵖ` for the non-commutative case. -/
@[to_additive "When the `add_group` is commutative, `equiv.neg` is an `add_equiv`.", simps apply]
def MulEquiv.inv (G : Type _) [DivisionCommMonoid G] : G ≃* G :=
  { Equiv.inv G with toFun := Inv.inv, invFun := Inv.inv, map_mul' := mul_inv }

@[simp]
theorem MulEquiv.inv_symm (G : Type _) [DivisionCommMonoid G] : (MulEquiv.inv G).symm = MulEquiv.inv G :=
  rfl

