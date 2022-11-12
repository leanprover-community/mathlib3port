/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Ring.Defs
import Mathbin.Algebra.Group.Commute
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites
import Mathbin.Algebra.Ring.InjSurj

/-!
# Semirings and rings

This file gives lemmas about semirings, rings and domains.
This is analogous to `algebra.group.basic`,
the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

For the definitions of semirings and rings see `algebra.ring.defs`.

-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_add r⟩
#align add_hom.mul_left AddHom.mulLeft

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mul _ _ r⟩
#align add_hom.mul_right AddHom.mulRight

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiring α] [NonAssocSemiring β] [AddHomClass F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _
#align map_bit0 map_bit0

end AddHomClass

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun := (· * ·) r
  map_zero' := mul_zero r
  map_add' := mul_add r
#align add_monoid_hom.mul_left AddMonoidHom.mulLeft

@[simp]
theorem coe_mul_left {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulLeft r) = (· * ·) r :=
  rfl
#align add_monoid_hom.coe_mul_left AddMonoidHom.coe_mul_left

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r
#align add_monoid_hom.mul_right AddMonoidHom.mulRight

@[simp]
theorem coe_mul_right {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulRight r) = (· * r) :=
  rfl
#align add_monoid_hom.coe_mul_right AddMonoidHom.coe_mul_right

theorem mul_right_apply {R : Type _} [NonUnitalNonAssocSemiring R] (a r : R) : mulRight r a = a * r :=
  rfl
#align add_monoid_hom.mul_right_apply AddMonoidHom.mul_right_apply

end AddMonoidHom

section HasDistribNeg

section Mul

variable [Mul α] [HasDistribNeg α]

namespace AddOpposite

instance : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.HasDistribNeg _ unop_neg unop_mul

end AddOpposite

open MulOpposite

instance : HasDistribNeg αᵐᵒᵖ :=
  { MulOpposite.hasInvolutiveNeg _ with neg_mul := fun _ _ => unop_injective <| mul_neg _ _,
    mul_neg := fun _ _ => unop_injective <| neg_mul _ _ }

end Mul

section Group

variable [Group α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, mul_left_inv]
#align inv_neg' inv_neg'

end Group

end HasDistribNeg

namespace Units

section HasDistribNeg

variable [Monoid α] [HasDistribNeg α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : Neg αˣ :=
  ⟨fun u => ⟨-↑u, -↑u⁻¹, by simp, by simp⟩⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem coe_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl
#align units.coe_neg Units.coe_neg

@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl
#align units.coe_neg_one Units.coe_neg_one

instance : HasDistribNeg αˣ :=
  Units.ext.HasDistribNeg _ Units.coe_neg Units.coe_mul

@[field_simps]
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]
#align units.neg_divp Units.neg_divp

end HasDistribNeg

section Ring

variable [Ring α] {a b : α}

@[field_simps]
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by simp only [divp, add_mul]
#align units.divp_add_divp_same Units.divp_add_divp_same

@[field_simps]
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]
#align units.divp_sub_divp_same Units.divp_sub_divp_same

@[field_simps]
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.add_divp Units.add_divp

@[field_simps]
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]
#align units.sub_divp Units.sub_divp

@[field_simps]
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]
#align units.divp_add Units.divp_add

@[field_simps]
theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  assoc_rw [Units.mul_inv, mul_one]
#align units.divp_sub Units.divp_sub

end Ring

end Units

theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit
#align is_unit.neg IsUnit.neg

@[simp]
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩
#align is_unit.neg_iff IsUnit.neg_iff

theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl
#align is_unit.sub_iff IsUnit.sub_iff

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

attribute [local simp] add_assoc add_comm add_left_comm mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = x * (b - x) := (eq_neg_of_add_eq_zero_right h).trans (by simp [mul_sub, mul_comm])
  refine' ⟨b - x, _, by simp, by rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]
#align Vieta_formula_quadratic Vieta_formula_quadratic

end NonUnitalCommRing

theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))
#align succ_ne_self succ_ne_self

theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))
#align pred_ne_self pred_ne_self

namespace SemiconjBy

@[simp]
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]
#align semiconj_by.add_right SemiconjBy.add_right

@[simp]
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a + b) x y :=
  by simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]
#align semiconj_by.add_left SemiconjBy.add_left

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_right SemiconjBy.neg_right

@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩
#align semiconj_by.neg_right_iff SemiconjBy.neg_right_iff

theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by simp only [SemiconjBy, h.eq, neg_mul, mul_neg]
#align semiconj_by.neg_left SemiconjBy.neg_left

@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩
#align semiconj_by.neg_left_iff SemiconjBy.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R] {a x y : R}

@[simp]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) :=
  (one_right a).neg_right
#align semiconj_by.neg_one_right SemiconjBy.neg_one_right

@[simp]
theorem neg_one_left (x : R) : SemiconjBy (-1) x x :=
  (SemiconjBy.one_left x).neg_left
#align semiconj_by.neg_one_left SemiconjBy.neg_one_left

end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x - x') (y - y') := by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right
#align semiconj_by.sub_right SemiconjBy.sub_right

@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left
#align semiconj_by.sub_left SemiconjBy.sub_left

end

end SemiconjBy

namespace Commute

/- warning: commute.add_right -> Commute.add_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a b) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a (HAdd.hAdd.{x x x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) b c))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.236 : Semiring.{u_1} R] {a : R} {b : R} {c : R}, (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a b) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))))) b c))
Case conversion may be inaccurate. Consider using '#align commute.add_right Commute.add_rightₓ'. -/
@[simp]
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right
#align commute.add_right Commute.add_right

/- warning: commute.add_left -> Commute.add_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) b c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) (HAdd.hAdd.{x x x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) a b) c)
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.271 : Semiring.{u_1} R] {a : R} {b : R} {c : R}, (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) a c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) b c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))))) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.add_left Commute.add_leftₓ'. -/
@[simp]
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left
#align commute.add_left Commute.add_left

theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h
#align commute.bit0_right Commute.bit0_right

theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h
#align commute.bit0_left Commute.bit0_left

theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)
#align commute.bit1_right Commute.bit1_right

theorem bit1_left [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)
#align commute.bit1_left Commute.bit1_left

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq Commute.mul_self_sub_mul_self_eq

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]
#align commute.mul_self_sub_mul_self_eq' Commute.mul_self_sub_mul_self_eq'

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) :
    a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm', sub_eq_zero, add_eq_zero_iff_eq_neg]
#align commute.mul_self_eq_mul_self_iff Commute.mul_self_eq_mul_self_iff

section

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right
#align commute.neg_right Commute.neg_right

@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff
#align commute.neg_right_iff Commute.neg_right_iff

theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left
#align commute.neg_left Commute.neg_left

@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff
#align commute.neg_left_iff Commute.neg_left_iff

end

section

variable [MulOneClass R] [HasDistribNeg R] {a : R}

@[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a
#align commute.neg_one_right Commute.neg_one_right

@[simp]
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a
#align commute.neg_one_left Commute.neg_one_left

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right
#align commute.sub_right Commute.sub_right

@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left
#align commute.sub_left Commute.sub_left

end

end Commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRing R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq
#align mul_self_sub_mul_self mul_self_sub_mul_self

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]
#align mul_self_sub_one mul_self_sub_one

theorem mul_self_eq_mul_self_iff [CommRing R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff
#align mul_self_eq_mul_self_iff mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]
#align mul_self_eq_one_iff mul_self_eq_one_iff

namespace Units

@[field_simps]
theorem divp_add_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) : a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, coe_mul]
  rw [mul_comm (↑u₁ * b), mul_comm b]
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one]
#align units.divp_add_divp Units.divp_add_divp

@[field_simps]
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) : a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]
#align units.divp_sub_divp Units.divp_sub_divp

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [ext_iff]
  push_cast
  exact mul_self_eq_one_iff
#align units.inv_eq_self_iff Units.inv_eq_self_iff

end Units

