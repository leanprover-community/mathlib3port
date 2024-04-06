/-
Copyright (c) 2018 Johan Commelin All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Algebra.Group.Hom.Defs
import Algebra.Group.Units

#align_import algebra.hom.units from "leanprover-community/mathlib"@"a07d750983b94c530ab69a726862c2ab6802b38c"

/-!
# Monoid homomorphisms and units

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `units` that depend on `monoid_hom`.

## Main declarations

* `units.map`: Turn an homomorphism from `α` to `β` monoids into an homomorphism from `αˣ` to `βˣ`.
* `monoid_hom.to_hom_units`: Turn an homomorphism from a group `α` to `β` into an homomorphism from
  `α` to `βˣ`.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `group` lemmas.
-/


open Function

universe u v w

#print Group.isUnit /-
@[to_additive]
theorem Group.isUnit {G} [Group G] (g : G) : IsUnit g :=
  ⟨⟨g, g⁻¹, mul_inv_self g, inv_mul_self g⟩, rfl⟩
#align group.is_unit Group.isUnit
#align add_group.is_add_unit AddGroup.isAddUnit
-/

section MonoidHomClass

#print IsUnit.eq_on_inv /-
/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive
      "If two homomorphisms from a subtraction monoid to an additive monoid are equal at an\nadditive unit `x`, then they are equal at `-x`."]
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [MonoidHomClass F G N] {x : G}
    (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel) <|
    h.symm ▸ map_mul_eq_one g <| hx.mul_inv_cancel
#align is_unit.eq_on_inv IsUnit.eq_on_inv
#align is_add_unit.eq_on_neg IsAddUnit.eq_on_neg
-/

#print eq_on_inv /-
/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
      "If two homomorphism from an additive group to an additive monoid are equal at `x`,\nthen they are equal at `-x`."]
theorem eq_on_inv {F G M} [Group G] [Monoid M] [MonoidHomClass F G M] (f g : F) {x : G}
    (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h
#align eq_on_inv eq_on_inv
#align eq_on_neg eq_on_neg
-/

end MonoidHomClass

namespace Units

variable {α : Type _} {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

#print Units.map /-
/-- The group homomorphism on units induced by a `monoid_hom`. -/
@[to_additive "The `add_group` homomorphism on `add_unit`s induced by an `add_monoid_hom`."]
def map (f : M →* N) : Mˣ →* Nˣ :=
  MonoidHom.mk'
    (fun u =>
      ⟨f u.val, f u.inv, by rw [← f.map_mul, u.val_inv, f.map_one], by
        rw [← f.map_mul, u.inv_val, f.map_one]⟩)
    fun x y => ext (f.map_hMul x y)
#align units.map Units.map
#align add_units.map AddUnits.map
-/

#print Units.coe_map /-
@[simp, to_additive]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x :=
  rfl
#align units.coe_map Units.coe_map
#align add_units.coe_map AddUnits.coe_map
-/

#print Units.coe_map_inv /-
@[simp, to_additive]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ :=
  rfl
#align units.coe_map_inv Units.coe_map_inv
#align add_units.coe_map_neg AddUnits.coe_map_neg
-/

#print Units.map_comp /-
@[simp, to_additive]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) :=
  rfl
#align units.map_comp Units.map_comp
#align add_units.map_comp AddUnits.map_comp
-/

variable (M)

#print Units.map_id /-
@[simp, to_additive]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := by ext <;> rfl
#align units.map_id Units.map_id
#align add_units.map_id AddUnits.map_id
-/

#print Units.coeHom /-
/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `add_units M → M` as an add_monoid homomorphism."]
def coeHom : Mˣ →* M :=
  ⟨coe, val_one, val_mul⟩
#align units.coe_hom Units.coeHom
#align add_units.coe_hom AddUnits.coeHom
-/

variable {M}

#print Units.coeHom_apply /-
@[simp, to_additive]
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x :=
  rfl
#align units.coe_hom_apply Units.coeHom_apply
#align add_units.coe_hom_apply AddUnits.coeHom_apply
-/

#print Units.val_pow_eq_pow_val /-
@[simp, norm_cast, to_additive]
theorem val_pow_eq_pow_val (u : Mˣ) (n : ℕ) : ((u ^ n : Mˣ) : M) = u ^ n :=
  (Units.coeHom M).map_pow u n
#align units.coe_pow Units.val_pow_eq_pow_val
#align add_units.coe_nsmul AddUnits.val_nsmul_eq_nsmul_val
-/

section DivisionMonoid

variable [DivisionMonoid α]

#print Units.val_div_eq_div_val /-
@[simp, norm_cast, to_additive]
theorem val_div_eq_div_val : ∀ u₁ u₂ : αˣ, ↑(u₁ / u₂) = (u₁ / u₂ : α) :=
  (Units.coeHom α).map_div
#align units.coe_div Units.val_div_eq_div_val
-/

#print Units.val_zpow_eq_zpow_val /-
@[simp, norm_cast, to_additive]
theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = u ^ n :=
  (Units.coeHom α).map_zpow
#align units.coe_zpow Units.val_zpow_eq_zpow_val
#align add_units.coe_zsmul AddUnits.val_zsmul_eq_zsmul_val
-/

#print divp_eq_div /-
@[field_simps]
theorem divp_eq_div (a : α) (u : αˣ) : a /ₚ u = a / u := by rw [div_eq_mul_inv, divp, u.coe_inv]
#align divp_eq_div divp_eq_div
-/

#print map_units_inv /-
@[simp, to_additive]
theorem map_units_inv {F : Type _} [MonoidHomClass F M α] (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ :=
  ((f : M →* α).comp (Units.coeHom M)).map_inv u
#align map_units_inv map_units_inv
#align map_add_units_neg map_addUnits_neg
-/

end DivisionMonoid

#print Units.liftRight /-
/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
      "If a map `g : M → add_units N` agrees with a homomorphism `f : M →+ N`, then this map\nis an add_monoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, ↑(g x) = f x) : M →* Nˣ
    where
  toFun := g
  map_one' := Units.ext <| (h 1).symm ▸ f.map_one
  map_mul' x y := Units.ext <| by simp only [h, coe_mul, f.map_mul]
#align units.lift_right Units.liftRight
#align add_units.lift_right AddUnits.liftRight
-/

#print Units.coe_liftRight /-
@[simp, to_additive]
theorem coe_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    (liftRight f g h x : N) = f x :=
  h x
#align units.coe_lift_right Units.coe_liftRight
#align add_units.coe_lift_right AddUnits.coe_liftRight
-/

#print Units.mul_liftRight_inv /-
@[simp, to_additive]
theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 := by rw [Units.mul_inv_eq_iff_eq_mul, one_mul, coe_lift_right]
#align units.mul_lift_right_inv Units.mul_liftRight_inv
#align add_units.add_lift_right_neg AddUnits.add_liftRight_neg
-/

#print Units.liftRight_inv_mul /-
@[simp, to_additive]
theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, ↑(g x) = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 := by rw [Units.inv_mul_eq_iff_eq_mul, mul_one, coe_lift_right]
#align units.lift_right_inv_mul Units.liftRight_inv_mul
#align add_units.lift_right_neg_add AddUnits.liftRight_neg_add
-/

end Units

namespace MonoidHom

#print MonoidHom.toHomUnits /-
/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.to_hom_units` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
      "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,\nthen its image lies in the `add_units` of `M`,\nand `f.to_hom_units` is the corresponding homomorphism from `G` to `add_units M`."]
def toHomUnits {G M : Type _} [Group G] [Monoid M] (f : G →* M) : G →* Mˣ :=
  Units.liftRight f
    (fun g => ⟨f g, f g⁻¹, map_mul_eq_one f (mul_inv_self _), map_mul_eq_one f (inv_mul_self _)⟩)
    fun g => rfl
#align monoid_hom.to_hom_units MonoidHom.toHomUnits
#align add_monoid_hom.to_hom_add_units AddMonoidHom.toHomAddUnits
-/

#print MonoidHom.coe_toHomUnits /-
@[simp, to_additive]
theorem coe_toHomUnits {G M : Type _} [Group G] [Monoid M] (f : G →* M) (g : G) :
    (f.toHomUnits g : M) = f g :=
  rfl
#align monoid_hom.coe_to_hom_units MonoidHom.coe_toHomUnits
#align add_monoid_hom.coe_to_hom_add_units AddMonoidHom.coe_toHomAddUnits
-/

end MonoidHom

namespace IsUnit

variable {F G α M N : Type _}

section Monoid

variable [Monoid M] [Monoid N]

#print IsUnit.map /-
@[to_additive]
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩ <;> exact (Units.map (f : M →* N) y).IsUnit
#align is_unit.map IsUnit.map
#align is_add_unit.map IsAddUnit.map
-/

#print IsUnit.of_leftInverse /-
@[to_additive]
theorem of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g
#align is_unit.of_left_inverse IsUnit.of_leftInverse
#align is_add_unit.of_left_inverse IsAddUnit.of_leftInverse
-/

#print isUnit_map_of_leftInverse /-
@[to_additive]
theorem isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M] {f : F} {x : M}
    (g : G) (hfg : Function.LeftInverse g f) : IsUnit (f x) ↔ IsUnit x :=
  ⟨of_leftInverse g hfg, map _⟩
#align is_unit_map_of_left_inverse isUnit_map_of_leftInverse
#align is_add_unit_map_of_left_inverse isAddUnit_map_of_leftInverse
-/

#print IsUnit.liftRight /-
/-- If a homomorphism `f : M →* N` sends each element to an `is_unit`, then it can be lifted
to `f : M →* Nˣ`. See also `units.lift_right` for a computable version. -/
@[to_additive
      "If a homomorphism `f : M →+ N` sends each element to an `is_add_unit`, then it can be\nlifted to `f : M →+ add_units N`. See also `add_units.lift_right` for a computable version."]
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  Units.liftRight f (fun x => (hf x).Unit) fun x => rfl
#align is_unit.lift_right IsUnit.liftRight
#align is_add_unit.lift_right IsAddUnit.liftRight
-/

#print IsUnit.coe_liftRight /-
@[to_additive]
theorem coe_liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x :=
  rfl
#align is_unit.coe_lift_right IsUnit.coe_liftRight
#align is_add_unit.coe_lift_right IsAddUnit.coe_liftRight
-/

#print IsUnit.mul_liftRight_inv /-
@[simp, to_additive]
theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 :=
  Units.mul_liftRight_inv (fun y => rfl) x
#align is_unit.mul_lift_right_inv IsUnit.mul_liftRight_inv
#align is_add_unit.add_lift_right_neg IsAddUnit.add_liftRight_neg
-/

#print IsUnit.liftRight_inv_mul /-
@[simp, to_additive]
theorem liftRight_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 :=
  Units.liftRight_inv_mul (fun y => rfl) x
#align is_unit.lift_right_inv_mul IsUnit.liftRight_inv_mul
#align is_add_unit.lift_right_neg_add IsAddUnit.liftRight_neg_add
-/

end Monoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

#print IsUnit.unit' /-
/-- The element of the group of units, corresponding to an element of a monoid which is a unit. As
opposed to `is_unit.unit`, the inverse is computable and comes from the inversion on `α`. This is
useful to transfer properties of inversion in `units α` to `α`. See also `to_units`. -/
@[to_additive
      "The element of the additive group of additive units, corresponding to an element of\nan additive monoid which is an additive unit. As opposed to `is_add_unit.add_unit`, the negation is\ncomputable and comes from the negation on `α`. This is useful to transfer properties of negation in\n`add_units α` to `α`. See also `to_add_units`.",
  simps]
def unit' (h : IsUnit a) : αˣ :=
  ⟨a, a⁻¹, h.mul_inv_cancel, h.inv_mul_cancel⟩
#align is_unit.unit' IsUnit.unit'
#align is_add_unit.add_unit' IsAddUnit.addUnit'
-/

#print IsUnit.mul_inv_cancel_left /-
@[simp, to_additive]
protected theorem mul_inv_cancel_left (h : IsUnit a) : ∀ b, a * (a⁻¹ * b) = b :=
  h.unit'.mul_inv_cancel_left
#align is_unit.mul_inv_cancel_left IsUnit.mul_inv_cancel_left
#align is_add_unit.add_neg_cancel_left IsAddUnit.add_neg_cancel_left
-/

#print IsUnit.inv_mul_cancel_left /-
@[simp, to_additive]
protected theorem inv_mul_cancel_left (h : IsUnit a) : ∀ b, a⁻¹ * (a * b) = b :=
  h.unit'.inv_mul_cancel_left
#align is_unit.inv_mul_cancel_left IsUnit.inv_mul_cancel_left
#align is_add_unit.neg_add_cancel_left IsAddUnit.neg_add_cancel_left
-/

#print IsUnit.mul_inv_cancel_right /-
@[simp, to_additive]
protected theorem mul_inv_cancel_right (h : IsUnit b) (a : α) : a * b * b⁻¹ = a :=
  h.unit'.mul_inv_cancel_right _
#align is_unit.mul_inv_cancel_right IsUnit.mul_inv_cancel_right
#align is_add_unit.add_neg_cancel_right IsAddUnit.add_neg_cancel_right
-/

#print IsUnit.inv_mul_cancel_right /-
@[simp, to_additive]
protected theorem inv_mul_cancel_right (h : IsUnit b) (a : α) : a * b⁻¹ * b = a :=
  h.unit'.inv_mul_cancel_right _
#align is_unit.inv_mul_cancel_right IsUnit.inv_mul_cancel_right
#align is_add_unit.neg_add_cancel_right IsAddUnit.neg_add_cancel_right
-/

#print IsUnit.div_self /-
@[to_additive]
protected theorem div_self (h : IsUnit a) : a / a = 1 := by rw [div_eq_mul_inv, h.mul_inv_cancel]
#align is_unit.div_self IsUnit.div_self
#align is_add_unit.sub_self IsAddUnit.sub_self
-/

#print IsUnit.eq_mul_inv_iff_mul_eq /-
@[to_additive]
protected theorem eq_mul_inv_iff_mul_eq (h : IsUnit c) : a = b * c⁻¹ ↔ a * c = b :=
  h.unit'.eq_mul_inv_iff_mul_eq
#align is_unit.eq_mul_inv_iff_mul_eq IsUnit.eq_mul_inv_iff_mul_eq
#align is_add_unit.eq_add_neg_iff_add_eq IsAddUnit.eq_add_neg_iff_add_eq
-/

#print IsUnit.eq_inv_mul_iff_mul_eq /-
@[to_additive]
protected theorem eq_inv_mul_iff_mul_eq (h : IsUnit b) : a = b⁻¹ * c ↔ b * a = c :=
  h.unit'.eq_inv_mul_iff_mul_eq
#align is_unit.eq_inv_mul_iff_mul_eq IsUnit.eq_inv_mul_iff_mul_eq
#align is_add_unit.eq_neg_add_iff_add_eq IsAddUnit.eq_neg_add_iff_add_eq
-/

#print IsUnit.inv_mul_eq_iff_eq_mul /-
@[to_additive]
protected theorem inv_mul_eq_iff_eq_mul (h : IsUnit a) : a⁻¹ * b = c ↔ b = a * c :=
  h.unit'.inv_mul_eq_iff_eq_mul
#align is_unit.inv_mul_eq_iff_eq_mul IsUnit.inv_mul_eq_iff_eq_mul
#align is_add_unit.neg_add_eq_iff_eq_add IsAddUnit.neg_add_eq_iff_eq_add
-/

#print IsUnit.mul_inv_eq_iff_eq_mul /-
@[to_additive]
protected theorem mul_inv_eq_iff_eq_mul (h : IsUnit b) : a * b⁻¹ = c ↔ a = c * b :=
  h.unit'.mul_inv_eq_iff_eq_mul
#align is_unit.mul_inv_eq_iff_eq_mul IsUnit.mul_inv_eq_iff_eq_mul
#align is_add_unit.add_neg_eq_iff_eq_add IsAddUnit.add_neg_eq_iff_eq_add
-/

#print IsUnit.mul_inv_eq_one /-
@[to_additive]
protected theorem mul_inv_eq_one (h : IsUnit b) : a * b⁻¹ = 1 ↔ a = b :=
  @Units.mul_inv_eq_one _ _ h.unit' _
#align is_unit.mul_inv_eq_one IsUnit.mul_inv_eq_one
#align is_add_unit.add_neg_eq_zero IsAddUnit.add_neg_eq_zero
-/

#print IsUnit.inv_mul_eq_one /-
@[to_additive]
protected theorem inv_mul_eq_one (h : IsUnit a) : a⁻¹ * b = 1 ↔ a = b :=
  @Units.inv_mul_eq_one _ _ h.unit' _
#align is_unit.inv_mul_eq_one IsUnit.inv_mul_eq_one
#align is_add_unit.neg_add_eq_zero IsAddUnit.neg_add_eq_zero
-/

#print IsUnit.mul_eq_one_iff_eq_inv /-
@[to_additive]
protected theorem mul_eq_one_iff_eq_inv (h : IsUnit b) : a * b = 1 ↔ a = b⁻¹ :=
  @Units.mul_eq_one_iff_eq_inv _ _ h.unit' _
#align is_unit.mul_eq_one_iff_eq_inv IsUnit.mul_eq_one_iff_eq_inv
#align is_add_unit.add_eq_zero_iff_eq_neg IsAddUnit.add_eq_zero_iff_eq_neg
-/

#print IsUnit.mul_eq_one_iff_inv_eq /-
@[to_additive]
protected theorem mul_eq_one_iff_inv_eq (h : IsUnit a) : a * b = 1 ↔ a⁻¹ = b :=
  @Units.mul_eq_one_iff_inv_eq _ _ h.unit' _
#align is_unit.mul_eq_one_iff_inv_eq IsUnit.mul_eq_one_iff_inv_eq
#align is_add_unit.add_eq_zero_iff_neg_eq IsAddUnit.add_eq_zero_iff_neg_eq
-/

#print IsUnit.div_mul_cancel /-
@[simp, to_additive]
protected theorem div_mul_cancel (h : IsUnit b) (a : α) : a / b * b = a := by
  rw [div_eq_mul_inv, h.inv_mul_cancel_right]
#align is_unit.div_mul_cancel IsUnit.div_mul_cancel
#align is_add_unit.sub_add_cancel IsAddUnit.sub_add_cancel
-/

/- warning: is_unit.mul_div_cancel clashes with mul_div_cancel'' -> mul_div_cancel_right
Case conversion may be inaccurate. Consider using '#align is_unit.mul_div_cancel mul_div_cancel_rightₓ'. -/
#print mul_div_cancel_right /-
@[simp, to_additive]
protected theorem mul_div_cancel_right (h : IsUnit b) (a : α) : a * b / b = a := by
  rw [div_eq_mul_inv, h.mul_inv_cancel_right]
#align is_unit.mul_div_cancel mul_div_cancel_right
#align add_sub_cancel add_sub_cancel_right
-/

#print IsUnit.mul_one_div_cancel /-
@[to_additive]
protected theorem mul_one_div_cancel (h : IsUnit a) : a * (1 / a) = 1 := by simp [h]
#align is_unit.mul_one_div_cancel IsUnit.mul_one_div_cancel
#align is_add_unit.add_zero_sub_cancel IsAddUnit.add_zero_sub_cancel
-/

#print IsUnit.one_div_mul_cancel /-
@[to_additive]
protected theorem one_div_mul_cancel (h : IsUnit a) : 1 / a * a = 1 := by simp [h]
#align is_unit.one_div_mul_cancel IsUnit.one_div_mul_cancel
#align is_add_unit.zero_sub_add_cancel IsAddUnit.zero_sub_add_cancel
-/

#print IsUnit.inv /-
@[to_additive]
theorem inv : IsUnit a → IsUnit a⁻¹ := by rintro ⟨u, rfl⟩; rw [← Units.val_inv_eq_inv_val];
  exact Units.isUnit _
#align is_unit.inv IsUnit.inv
#align is_add_unit.neg IsAddUnit.neg
-/

#print IsUnit.div /-
@[to_additive]
theorem div (ha : IsUnit a) (hb : IsUnit b) : IsUnit (a / b) := by rw [div_eq_mul_inv];
  exact ha.mul hb.inv
#align is_unit.div IsUnit.div
#align is_add_unit.sub IsAddUnit.sub
-/

#print IsUnit.div_left_inj /-
@[to_additive]
protected theorem div_left_inj (h : IsUnit c) : a / c = b / c ↔ a = b := by
  simp_rw [div_eq_mul_inv]; exact Units.mul_left_inj h.inv.unit'
#align is_unit.div_left_inj IsUnit.div_left_inj
#align is_add_unit.sub_left_inj IsAddUnit.sub_left_inj
-/

#print IsUnit.div_eq_iff /-
@[to_additive]
protected theorem div_eq_iff (h : IsUnit b) : a / b = c ↔ a = c * b := by
  rw [div_eq_mul_inv, h.mul_inv_eq_iff_eq_mul]
#align is_unit.div_eq_iff IsUnit.div_eq_iff
#align is_add_unit.sub_eq_iff IsAddUnit.sub_eq_iff
-/

#print IsUnit.eq_div_iff /-
@[to_additive]
protected theorem eq_div_iff (h : IsUnit c) : a = b / c ↔ a * c = b := by
  rw [div_eq_mul_inv, h.eq_mul_inv_iff_mul_eq]
#align is_unit.eq_div_iff IsUnit.eq_div_iff
#align is_add_unit.eq_sub_iff IsAddUnit.eq_sub_iff
-/

#print IsUnit.div_eq_of_eq_mul /-
@[to_additive]
protected theorem div_eq_of_eq_mul (h : IsUnit b) : a = c * b → a / b = c :=
  h.div_eq_iff.2
#align is_unit.div_eq_of_eq_mul IsUnit.div_eq_of_eq_mul
#align is_add_unit.sub_eq_of_eq_add IsAddUnit.sub_eq_of_eq_add
-/

#print IsUnit.eq_div_of_mul_eq /-
@[to_additive]
protected theorem eq_div_of_mul_eq (h : IsUnit c) : a * c = b → a = b / c :=
  h.eq_div_iff.2
#align is_unit.eq_div_of_mul_eq IsUnit.eq_div_of_mul_eq
#align is_add_unit.eq_sub_of_add_eq IsAddUnit.eq_sub_of_add_eq
-/

#print IsUnit.div_eq_one_iff_eq /-
@[to_additive]
protected theorem div_eq_one_iff_eq (h : IsUnit b) : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun hab => hab.symm ▸ h.div_self⟩
#align is_unit.div_eq_one_iff_eq IsUnit.div_eq_one_iff_eq
#align is_add_unit.sub_eq_zero_iff_eq IsAddUnit.sub_eq_zero_iff_eq
-/

#print IsUnit.div_mul_left /-
/-- The `group` version of this lemma is `div_mul_cancel'''` -/
@[to_additive "The `add_group` version of this lemma is `sub_add_cancel''`"]
protected theorem div_mul_left (h : IsUnit b) : b / (a * b) = 1 / a := by
  rw [div_eq_mul_inv, mul_inv_rev, h.mul_inv_cancel_left, one_div]
#align is_unit.div_mul_left IsUnit.div_mul_left
#align is_add_unit.sub_add_left IsAddUnit.sub_add_left
-/

#print IsUnit.mul_div_mul_right /-
@[to_additive]
protected theorem mul_div_mul_right (h : IsUnit c) (a b : α) : a * c / (b * c) = a / b := by
  simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc, h.mul_inv_cancel_left]
#align is_unit.mul_div_mul_right IsUnit.mul_div_mul_right
#align is_add_unit.add_sub_add_right IsAddUnit.add_sub_add_right
-/

#print IsUnit.mul_mul_div /-
@[to_additive]
protected theorem mul_mul_div (a : α) (h : IsUnit b) : a * b * (1 / b) = a := by simp [h]
#align is_unit.mul_mul_div IsUnit.mul_mul_div
#align is_add_unit.add_add_sub IsAddUnit.add_add_sub
-/

end DivisionMonoid

section DivisionCommMonoid

variable [DivisionCommMonoid α] {a b c d : α}

#print IsUnit.div_mul_right /-
@[to_additive]
protected theorem div_mul_right (h : IsUnit a) (b : α) : a / (a * b) = 1 / b := by
  rw [mul_comm, h.div_mul_left]
#align is_unit.div_mul_right IsUnit.div_mul_right
#align is_add_unit.sub_add_right IsAddUnit.sub_add_right
-/

/- warning: is_unit.mul_div_cancel_left clashes with mul_div_cancel''' -> mul_div_cancel_left
Case conversion may be inaccurate. Consider using '#align is_unit.mul_div_cancel_left mul_div_cancel_leftₓ'. -/
#print mul_div_cancel_left /-
@[to_additive]
protected theorem mul_div_cancel_left (h : IsUnit a) (b : α) : a * b / a = b := by
  rw [mul_comm, h.mul_div_cancel]
#align is_unit.mul_div_cancel_left mul_div_cancel_left
#align add_sub_cancel' add_sub_cancel_left
-/

#print IsUnit.mul_div_cancel /-
@[to_additive]
protected theorem mul_div_cancel (h : IsUnit a) (b : α) : a * (b / a) = b := by
  rw [mul_comm, h.div_mul_cancel]
#align is_unit.mul_div_cancel' IsUnit.mul_div_cancel
#align is_add_unit.add_sub_cancel' IsAddUnit.add_sub_cancel
-/

#print IsUnit.mul_div_mul_left /-
@[to_additive]
protected theorem mul_div_mul_left (h : IsUnit c) (a b : α) : c * a / (c * b) = a / b := by
  rw [mul_comm c, mul_comm c, h.mul_div_mul_right]
#align is_unit.mul_div_mul_left IsUnit.mul_div_mul_left
#align is_add_unit.add_sub_add_left IsAddUnit.add_sub_add_left
-/

#print IsUnit.mul_eq_mul_of_div_eq_div /-
@[to_additive]
protected theorem mul_eq_mul_of_div_eq_div (hb : IsUnit b) (hd : IsUnit d) (a c : α)
    (h : a / b = c / d) : a * d = c * b := by
  rw [← mul_one a, ← hb.div_self, ← mul_comm_div, h, div_mul_eq_mul_div, hd.div_mul_cancel]
#align is_unit.mul_eq_mul_of_div_eq_div IsUnit.mul_eq_mul_of_div_eq_div
#align is_add_unit.add_eq_add_of_sub_eq_sub IsAddUnit.add_eq_add_of_sub_eq_sub
-/

#print IsUnit.div_eq_div_iff /-
@[to_additive]
protected theorem div_eq_div_iff (hb : IsUnit b) (hd : IsUnit d) : a / b = c / d ↔ a * d = c * b :=
  by
  rw [← (hb.mul hd).mul_left_inj, ← mul_assoc, hb.div_mul_cancel, ← mul_assoc, mul_right_comm,
    hd.div_mul_cancel]
#align is_unit.div_eq_div_iff IsUnit.div_eq_div_iff
#align is_add_unit.sub_eq_sub_iff IsAddUnit.sub_eq_sub_iff
-/

#print IsUnit.div_div_cancel /-
@[to_additive]
protected theorem div_div_cancel (h : IsUnit a) : a / (a / b) = b := by
  rw [div_div_eq_mul_div, h.mul_div_cancel_left]
#align is_unit.div_div_cancel IsUnit.div_div_cancel
#align is_add_unit.sub_sub_cancel IsAddUnit.sub_sub_cancel
-/

#print IsUnit.div_div_cancel_left /-
@[to_additive]
protected theorem div_div_cancel_left (h : IsUnit a) : a / b / a = b⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_right_comm, h.mul_inv_cancel, one_mul]
#align is_unit.div_div_cancel_left IsUnit.div_div_cancel_left
#align is_add_unit.sub_sub_cancel_left IsAddUnit.sub_sub_cancel_left
-/

end DivisionCommMonoid

end IsUnit

