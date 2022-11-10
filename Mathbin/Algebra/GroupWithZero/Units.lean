/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.GroupWithZero.Basic
import Mathbin.Algebra.Hom.Units
import Mathbin.GroupTheory.GroupAction.Units

/-!
# Lemmas about units in a `monoid_with_zero` or a `group_with_zero`.

We also define `ring.inverse`, a globally defined function on any ring
(in fact any `monoid_with_zero`), which inverts units and sends non-units to zero.
-/


variable {α M₀ G₀ M₀' G₀' F F' : Type _}

variable [MonoidWithZero M₀]

namespace Units

/-- An element of the unit group of a nonzero monoid with zero represented as an element
    of the monoid is nonzero. -/
@[simp]
theorem ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) ≠ 0 :=
  left_ne_zero_of_mul_eq_one u.mul_inv

-- We can't use `mul_eq_zero` + `units.ne_zero` in the next two lemmas because we don't assume
-- `nonzero M₀`.
@[simp]
theorem mul_left_eq_zero (u : M₀ˣ) {a : M₀} : a * u = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_left h ↑u⁻¹, fun h => mul_eq_zero_of_left h u⟩

@[simp]
theorem mul_right_eq_zero (u : M₀ˣ) {a : M₀} : ↑u * a = 0 ↔ a = 0 :=
  ⟨fun h => by simpa using mul_eq_zero_of_right (↑u⁻¹) h, mul_eq_zero_of_right u⟩

end Units

namespace IsUnit

theorem ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a ≠ 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.NeZero

theorem mul_right_eq_zero {a b : M₀} (ha : IsUnit a) : a * b = 0 ↔ b = 0 :=
  let ⟨u, hu⟩ := ha
  hu ▸ u.mul_right_eq_zero

theorem mul_left_eq_zero {a b : M₀} (hb : IsUnit b) : a * b = 0 ↔ a = 0 :=
  let ⟨u, hu⟩ := hb
  hu ▸ u.mul_left_eq_zero

end IsUnit

@[simp]
theorem is_unit_zero_iff : IsUnit (0 : M₀) ↔ (0 : M₀) = 1 :=
  ⟨fun ⟨⟨_, a, (a0 : 0 * a = 1), _⟩, rfl⟩ => by rwa [zero_mul] at a0, fun h =>
    @is_unit_of_subsingleton _ _ (subsingleton_of_zero_eq_one h) 0⟩

@[simp]
theorem not_is_unit_zero [Nontrivial M₀] : ¬IsUnit (0 : M₀) :=
  mt is_unit_zero_iff.1 zero_ne_one

namespace Ring

open Classical

/-- Introduce a function `inverse` on a monoid with zero `M₀`, which sends `x` to `x⁻¹` if `x` is
invertible and to `0` otherwise.  This definition is somewhat ad hoc, but one needs a fully (rather
than partially) defined inverse function for some purposes, including for calculus.

Note that while this is in the `ring` namespace for brevity, it requires the weaker assumption
`monoid_with_zero M₀` instead of `ring M₀`. -/
noncomputable def inverse : M₀ → M₀ := fun x => if h : IsUnit x then ((h.Unit⁻¹ : M₀ˣ) : M₀) else 0

/-- By definition, if `x` is invertible then `inverse x = x⁻¹`. -/
@[simp]
theorem inverse_unit (u : M₀ˣ) : inverse (u : M₀) = (u⁻¹ : M₀ˣ) := by
  simp only [Units.is_unit, inverse, dif_pos]
  exact Units.inv_unique rfl

/-- By definition, if `x` is not invertible then `inverse x = 0`. -/
@[simp]
theorem inverse_non_unit (x : M₀) (h : ¬IsUnit x) : inverse x = 0 :=
  dif_neg h

theorem mul_inverse_cancel (x : M₀) (h : IsUnit x) : x * inverse x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.mul_inv]

theorem inverse_mul_cancel (x : M₀) (h : IsUnit x) : inverse x * x = 1 := by
  rcases h with ⟨u, rfl⟩
  rw [inverse_unit, Units.inv_mul]

theorem mul_inverse_cancel_right (x y : M₀) (h : IsUnit x) : y * x * inverse x = y := by
  rw [mul_assoc, mul_inverse_cancel x h, mul_one]

theorem inverse_mul_cancel_right (x y : M₀) (h : IsUnit x) : y * inverse x * x = y := by
  rw [mul_assoc, inverse_mul_cancel x h, mul_one]

theorem mul_inverse_cancel_left (x y : M₀) (h : IsUnit x) : x * (inverse x * y) = y := by
  rw [← mul_assoc, mul_inverse_cancel x h, one_mul]

theorem inverse_mul_cancel_left (x y : M₀) (h : IsUnit x) : inverse x * (x * y) = y := by
  rw [← mul_assoc, inverse_mul_cancel x h, one_mul]

theorem inverse_mul_eq_iff_eq_mul (x y z : M₀) (h : IsUnit x) : inverse x * y = z ↔ y = x * z :=
  ⟨fun h1 => by rw [← h1, mul_inverse_cancel_left _ _ h], fun h1 => by rw [h1, inverse_mul_cancel_left _ _ h]⟩

theorem eq_mul_inverse_iff_mul_eq (x y z : M₀) (h : IsUnit z) : x = y * inverse z ↔ x * z = y :=
  ⟨fun h1 => by rw [h1, inverse_mul_cancel_right _ _ h], fun h1 => by rw [← h1, mul_inverse_cancel_right _ _ h]⟩

variable (M₀)

@[simp]
theorem inverse_one : inverse (1 : M₀) = 1 :=
  inverse_unit 1

@[simp]
theorem inverse_zero : inverse (0 : M₀) = 0 := by
  nontriviality
  exact inverse_non_unit _ not_is_unit_zero

variable {M₀}

theorem mul_inverse_rev' {a b : M₀} (h : Commute a b) : inverse (a * b) = inverse b * inverse a := by
  by_cases hab:IsUnit (a * b)
  · obtain ⟨⟨a, rfl⟩, b, rfl⟩ := h.is_unit_mul_iff.mp hab
    rw [← Units.coe_mul, inverse_unit, inverse_unit, inverse_unit, ← Units.coe_mul, mul_inv_rev]
    
  obtain ha | hb := not_and_distrib.mp (mt h.is_unit_mul_iff.mpr hab)
  · rw [inverse_non_unit _ hab, inverse_non_unit _ ha, mul_zero]
    
  · rw [inverse_non_unit _ hab, inverse_non_unit _ hb, zero_mul]
    

theorem mul_inverse_rev {M₀} [CommMonoidWithZero M₀] (a b : M₀) : Ring.inverse (a * b) = inverse b * inverse a :=
  mul_inverse_rev' (Commute.all _ _)

end Ring

theorem IsUnit.ring_inverse {a : M₀} : IsUnit a → IsUnit (Ring.inverse a)
  | ⟨u, hu⟩ => hu ▸ ⟨u⁻¹, (Ring.inverse_unit u).symm⟩

@[simp]
theorem is_unit_ring_inverse {a : M₀} : IsUnit (Ring.inverse a) ↔ IsUnit a :=
  ⟨fun h => by
    cases subsingleton_or_nontrivial M₀
    · convert h
      
    · contrapose h
      rw [Ring.inverse_non_unit _ h]
      exact not_is_unit_zero
      ,
    IsUnit.ring_inverse⟩

theorem Commute.ring_inverse_ring_inverse {a b : M₀} (h : Commute a b) : Commute (Ring.inverse a) (Ring.inverse b) :=
  (Ring.mul_inverse_rev' h.symm).symm.trans <| (congr_arg _ h.symm.Eq).trans <| Ring.mul_inverse_rev' h

namespace Units

variable [GroupWithZero G₀]

variable {a b : G₀}

/-- Embed a non-zero element of a `group_with_zero` into the unit group.
  By combining this function with the operations on units,
  or the `/ₚ` operation, it is possible to write a division
  as a partial function with three arguments. -/
def mk0 (a : G₀) (ha : a ≠ 0) : G₀ˣ :=
  ⟨a, a⁻¹, mul_inv_cancel ha, inv_mul_cancel ha⟩

@[simp]
theorem mk0_one (h := one_ne_zero) : mk0 (1 : G₀) h = 1 := by
  ext
  rfl

@[simp]
theorem coe_mk0 {a : G₀} (h : a ≠ 0) : (mk0 a h : G₀) = a :=
  rfl

@[simp]
theorem mk0_coe (u : G₀ˣ) (h : (u : G₀) ≠ 0) : mk0 (u : G₀) h = u :=
  Units.ext rfl

@[simp]
theorem mul_inv' (u : G₀ˣ) : (u : G₀) * u⁻¹ = 1 :=
  mul_inv_cancel u.NeZero

@[simp]
theorem inv_mul' (u : G₀ˣ) : (u⁻¹ : G₀) * u = 1 :=
  inv_mul_cancel u.NeZero

@[simp]
theorem mk0_inj {a b : G₀} (ha : a ≠ 0) (hb : b ≠ 0) : Units.mk0 a ha = Units.mk0 b hb ↔ a = b :=
  ⟨fun h => by injection h, fun h => Units.ext h⟩

/-- In a group with zero, an existential over a unit can be rewritten in terms of `units.mk0`. -/
theorem exists0 {p : G₀ˣ → Prop} : (∃ g : G₀ˣ, p g) ↔ ∃ (g : G₀)(hg : g ≠ 0), p (Units.mk0 g hg) :=
  ⟨fun ⟨g, pg⟩ => ⟨g, g.NeZero, (g.mk0_coe g.NeZero).symm ▸ pg⟩, fun ⟨g, hg, pg⟩ => ⟨Units.mk0 g hg, pg⟩⟩

/-- An alternative version of `units.exists0`. This one is useful if Lean cannot
figure out `p` when using `units.exists0` from right to left. -/
theorem exists0' {p : ∀ g : G₀, g ≠ 0 → Prop} : (∃ (g : G₀)(hg : g ≠ 0), p g hg) ↔ ∃ g : G₀ˣ, p g g.NeZero :=
  Iff.trans (by simp_rw [coe_mk0]) exists0.symm

@[simp]
theorem exists_iff_ne_zero {x : G₀} : (∃ u : G₀ˣ, ↑u = x) ↔ x ≠ 0 := by simp [exists0]

theorem _root_.group_with_zero.eq_zero_or_unit (a : G₀) : a = 0 ∨ ∃ u : G₀ˣ, a = u := by
  by_cases h:a = 0
  · left
    exact h
    
  · right
    simpa only [eq_comm] using units.exists_iff_ne_zero.mpr h
    

@[simp]
theorem smul_mk0 {α : Type _} [HasSmul G₀ α] {g : G₀} (hg : g ≠ 0) (a : α) : mk0 g hg • a = g • a :=
  rfl

end Units

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

theorem IsUnit.mk0 (x : G₀) (hx : x ≠ 0) : IsUnit x :=
  (Units.mk0 x hx).IsUnit

theorem is_unit_iff_ne_zero : IsUnit a ↔ a ≠ 0 :=
  Units.exists_iff_ne_zero

alias is_unit_iff_ne_zero ↔ _ Ne.is_unit

attribute [protected] Ne.is_unit

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.no_zero_divisors : NoZeroDivisors G₀ :=
  { (‹_› : GroupWithZero G₀) with
    eq_zero_or_eq_zero_of_mul_eq_zero := fun a b h => by
      contrapose! h
      exact (Units.mk0 a h.1 * Units.mk0 b h.2).NeZero }

-- see Note [lower instance priority]
instance (priority := 10) GroupWithZero.cancelMonoidWithZero : CancelMonoidWithZero G₀ :=
  { (‹_› : GroupWithZero G₀) with
    mul_left_cancel_of_ne_zero := fun x y z hx h => by rw [← inv_mul_cancel_left₀ hx y, h, inv_mul_cancel_left₀ hx z],
    mul_right_cancel_of_ne_zero := fun x y z hy h => by
      rw [← mul_inv_cancel_right₀ hy x, h, mul_inv_cancel_right₀ hy z] }

-- Can't be put next to the other `mk0` lemmas because it depends on the
-- `no_zero_divisors` instance, which depends on `mk0`.
@[simp]
theorem Units.mk0_mul (x y : G₀) (hxy) :
    Units.mk0 (x * y) hxy = Units.mk0 x (mul_ne_zero_iff.mp hxy).1 * Units.mk0 y (mul_ne_zero_iff.mp hxy).2 := by
  ext
  rfl

@[simp]
theorem div_self (h : a ≠ 0) : a / a = 1 :=
  h.IsUnit.div_self

theorem eq_mul_inv_iff_mul_eq₀ (hc : c ≠ 0) : a = b * c⁻¹ ↔ a * c = b :=
  hc.IsUnit.eq_mul_inv_iff_mul_eq

theorem eq_inv_mul_iff_mul_eq₀ (hb : b ≠ 0) : a = b⁻¹ * c ↔ b * a = c :=
  hb.IsUnit.eq_inv_mul_iff_mul_eq

theorem inv_mul_eq_iff_eq_mul₀ (ha : a ≠ 0) : a⁻¹ * b = c ↔ b = a * c :=
  ha.IsUnit.inv_mul_eq_iff_eq_mul

theorem mul_inv_eq_iff_eq_mul₀ (hb : b ≠ 0) : a * b⁻¹ = c ↔ a = c * b :=
  hb.IsUnit.mul_inv_eq_iff_eq_mul

theorem mul_inv_eq_one₀ (hb : b ≠ 0) : a * b⁻¹ = 1 ↔ a = b :=
  hb.IsUnit.mul_inv_eq_one

theorem inv_mul_eq_one₀ (ha : a ≠ 0) : a⁻¹ * b = 1 ↔ a = b :=
  ha.IsUnit.inv_mul_eq_one

theorem mul_eq_one_iff_eq_inv₀ (hb : b ≠ 0) : a * b = 1 ↔ a = b⁻¹ :=
  hb.IsUnit.mul_eq_one_iff_eq_inv

theorem mul_eq_one_iff_inv_eq₀ (ha : a ≠ 0) : a * b = 1 ↔ a⁻¹ = b :=
  ha.IsUnit.mul_eq_one_iff_inv_eq

@[simp]
theorem div_mul_cancel (a : G₀) (h : b ≠ 0) : a / b * b = a :=
  h.IsUnit.div_mul_cancel _

@[simp]
theorem mul_div_cancel (a : G₀) (h : b ≠ 0) : a * b / b = a :=
  h.IsUnit.mul_div_cancel _

theorem mul_one_div_cancel (h : a ≠ 0) : a * (1 / a) = 1 :=
  h.IsUnit.mul_one_div_cancel

theorem one_div_mul_cancel (h : a ≠ 0) : 1 / a * a = 1 :=
  h.IsUnit.one_div_mul_cancel

theorem div_left_inj' (hc : c ≠ 0) : a / c = b / c ↔ a = b :=
  hc.IsUnit.div_left_inj

@[field_simps]
theorem div_eq_iff (hb : b ≠ 0) : a / b = c ↔ a = c * b :=
  hb.IsUnit.div_eq_iff

@[field_simps]
theorem eq_div_iff (hb : b ≠ 0) : c = a / b ↔ c * b = a :=
  hb.IsUnit.eq_div_iff

theorem div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
  hb.IsUnit.div_eq_iff.trans eq_comm

theorem eq_div_iff_mul_eq (hc : c ≠ 0) : a = b / c ↔ a * c = b :=
  hc.IsUnit.eq_div_iff

theorem div_eq_of_eq_mul (hb : b ≠ 0) : a = c * b → a / b = c :=
  hb.IsUnit.div_eq_of_eq_mul

theorem eq_div_of_mul_eq (hc : c ≠ 0) : a * c = b → a = b / c :=
  hc.IsUnit.eq_div_of_mul_eq

theorem div_eq_one_iff_eq (hb : b ≠ 0) : a / b = 1 ↔ a = b :=
  hb.IsUnit.div_eq_one_iff_eq

theorem div_mul_left (hb : b ≠ 0) : b / (a * b) = 1 / a :=
  hb.IsUnit.div_mul_left

theorem mul_div_mul_right (a b : G₀) (hc : c ≠ 0) : a * c / (b * c) = a / b :=
  hc.IsUnit.mul_div_mul_right _ _

theorem mul_mul_div (a : G₀) (hb : b ≠ 0) : a = a * b * (1 / b) :=
  (hb.IsUnit.mul_mul_div _).symm

theorem div_div_div_cancel_right (a : G₀) (hc : c ≠ 0) : a / c / (b / c) = a / b := by
  rw [div_div_eq_mul_div, div_mul_cancel _ hc]

theorem div_mul_div_cancel (a : G₀) (hc : c ≠ 0) : a / c * (c / b) = a / b := by
  rw [← mul_div_assoc, div_mul_cancel _ hc]

theorem div_mul_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a / b * b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (div_mul_cancel a)

theorem mul_div_cancel_of_imp {a b : G₀} (h : b = 0 → a = 0) : a * b / b = a :=
  Classical.by_cases (fun hb : b = 0 => by simp [*]) (mul_div_cancel a)

@[simp]
theorem divp_mk0 (a : G₀) {b : G₀} (hb : b ≠ 0) : a /ₚ Units.mk0 b hb = a / b :=
  divp_eq_div _ _

theorem div_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a / b ≠ 0 := by
  rw [div_eq_mul_inv]
  exact mul_ne_zero ha (inv_ne_zero hb)

@[simp]
theorem div_eq_zero_iff : a / b = 0 ↔ a = 0 ∨ b = 0 := by simp [div_eq_mul_inv]

theorem div_ne_zero_iff : a / b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  div_eq_zero_iff.Not.trans not_or

theorem Ring.inverse_eq_inv (a : G₀) : Ring.inverse a = a⁻¹ := by
  obtain rfl | ha := eq_or_ne a 0
  · simp
    
  · exact Ring.inverse_unit (Units.mk0 a ha)
    

@[simp]
theorem Ring.inverse_eq_inv' : (Ring.inverse : G₀ → G₀) = Inv.inv :=
  funext Ring.inverse_eq_inv

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

-- see Note [lower instance priority]
instance (priority := 10) CommGroupWithZero.cancelCommMonoidWithZero : CancelCommMonoidWithZero G₀ :=
  { GroupWithZero.cancelMonoidWithZero, CommGroupWithZero.toCommMonoidWithZero G₀ with }

-- See note [lower instance priority]
instance (priority := 100) CommGroupWithZero.toDivisionCommMonoid : DivisionCommMonoid G₀ :=
  { ‹CommGroupWithZero G₀›, GroupWithZero.toDivisionMonoid with }

theorem div_mul_right (b : G₀) (ha : a ≠ 0) : a / (a * b) = 1 / b :=
  ha.IsUnit.div_mul_right _

theorem mul_div_cancel_left_of_imp {a b : G₀} (h : a = 0 → b = 0) : a * b / a = b := by
  rw [mul_comm, mul_div_cancel_of_imp h]

theorem mul_div_cancel_left (b : G₀) (ha : a ≠ 0) : a * b / a = b :=
  ha.IsUnit.mul_div_cancel_left _

theorem mul_div_cancel_of_imp' {a b : G₀} (h : b = 0 → a = 0) : b * (a / b) = a := by
  rw [mul_comm, div_mul_cancel_of_imp h]

theorem mul_div_cancel' (a : G₀) (hb : b ≠ 0) : b * (a / b) = a :=
  hb.IsUnit.mul_div_cancel' _

theorem mul_div_mul_left (a b : G₀) (hc : c ≠ 0) : c * a / (c * b) = a / b :=
  hc.IsUnit.mul_div_mul_left _ _

theorem mul_eq_mul_of_div_eq_div (a : G₀) {b : G₀} (c : G₀) {d : G₀} (hb : b ≠ 0) (hd : d ≠ 0) (h : a / b = c / d) :
    a * d = c * b := by rw [← mul_one a, ← div_self hb, ← mul_comm_div, h, div_mul_eq_mul_div, div_mul_cancel _ hd]

@[field_simps]
theorem div_eq_div_iff (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = c * b :=
  hb.IsUnit.div_eq_div_iff hd.IsUnit

theorem div_div_cancel' (ha : a ≠ 0) : a / (a / b) = b :=
  ha.IsUnit.div_div_cancel

theorem div_helper (b : G₀) (h : a ≠ 0) : 1 / (a * b) * a = 1 / b := by
  rw [div_mul_eq_mul_div, one_mul, div_mul_right _ h]

end CommGroupWithZero

namespace SemiconjBy

@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : SemiconjBy a 0 0 := by simp only [SemiconjBy, mul_zero, zero_mul]

@[simp]
theorem zero_left [MulZeroClass G₀] (x y : G₀) : SemiconjBy 0 x y := by simp only [SemiconjBy, mul_zero, zero_mul]

variable [GroupWithZero G₀] {a x y x' y' : G₀}

@[simp]
theorem inv_symm_left_iff₀ : SemiconjBy a⁻¹ x y ↔ SemiconjBy a y x :=
  Classical.by_cases (fun ha : a = 0 => by simp only [ha, inv_zero, SemiconjBy.zero_left]) fun ha =>
    @units_inv_symm_left_iff _ _ (Units.mk0 a ha) _ _

theorem inv_symm_left₀ (h : SemiconjBy a x y) : SemiconjBy a⁻¹ y x :=
  SemiconjBy.inv_symm_left_iff₀.2 h

theorem inv_right₀ (h : SemiconjBy a x y) : SemiconjBy a x⁻¹ y⁻¹ := by
  by_cases ha:a = 0
  · simp only [ha, zero_left]
    
  by_cases hx:x = 0
  · subst x
    simp only [SemiconjBy, mul_zero, @eq_comm _ _ (y * a), mul_eq_zero] at h
    simp [h.resolve_right ha]
    
  · have := mul_ne_zero ha hx
    rw [h.eq, mul_ne_zero_iff] at this
    exact @units_inv_right _ _ _ (Units.mk0 x hx) (Units.mk0 y this.1) h
    

@[simp]
theorem inv_right_iff₀ : SemiconjBy a x⁻¹ y⁻¹ ↔ SemiconjBy a x y :=
  ⟨fun h => inv_inv x ▸ inv_inv y ▸ h.inv_right₀, inv_right₀⟩

theorem div_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x / x') (y / y') := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact h.mul_right h'.inv_right₀

end SemiconjBy

namespace Commute

/- warning: commute.zero_right -> Commute.zero_right is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) a (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2))))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.186 : Semiring.{u_1} R] (a : R), Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.186))) a (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.186))))
Case conversion may be inaccurate. Consider using '#align commute.zero_right Commute.zero_rightₓ'. -/
@[simp]
theorem zero_right [MulZeroClass G₀] (a : G₀) : Commute a 0 :=
  SemiconjBy.zero_right a

/- warning: commute.zero_left -> Commute.zero_left is a dubious translation:
lean 3 declaration is
  forall {G₀ : Type.{u_3}} [_inst_2 : MulZeroClass.{u_3} G₀] (a : G₀), Commute.{u_3} G₀ (MulZeroClass.toHasMul.{u_3} G₀ _inst_2) (OfNat.ofNat.{u_3} G₀ 0 (OfNat.mk.{u_3} G₀ 0 (Zero.zero.{u_3} G₀ (MulZeroClass.toHasZero.{u_3} G₀ _inst_2)))) a
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.211 : Semiring.{u_1} R] (a : R), Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.211))) (OfNat.ofNat.{u_1} R 0 (Zero.toOfNat0.{u_1} R (MonoidWithZero.toZero.{u_1} R (Semiring.toMonoidWithZero.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.211)))) a
Case conversion may be inaccurate. Consider using '#align commute.zero_left Commute.zero_leftₓ'. -/
@[simp]
theorem zero_left [MulZeroClass G₀] (a : G₀) : Commute 0 a :=
  SemiconjBy.zero_left a a

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem inv_left_iff₀ : Commute a⁻¹ b ↔ Commute a b :=
  SemiconjBy.inv_symm_left_iff₀

theorem inv_left₀ (h : Commute a b) : Commute a⁻¹ b :=
  inv_left_iff₀.2 h

@[simp]
theorem inv_right_iff₀ : Commute a b⁻¹ ↔ Commute a b :=
  SemiconjBy.inv_right_iff₀

theorem inv_right₀ (h : Commute a b) : Commute a b⁻¹ :=
  inv_right_iff₀.2 h

@[simp]
theorem div_right (hab : Commute a b) (hac : Commute a c) : Commute a (b / c) :=
  hab.div_right hac

@[simp]
theorem div_left (hac : Commute a c) (hbc : Commute b c) : Commute (a / b) c := by
  rw [div_eq_mul_inv]
  exact hac.mul_left hbc.inv_left₀

end Commute

section MonoidWithZero

variable [GroupWithZero G₀] [Nontrivial M₀] [MonoidWithZero M₀'] [MonoidWithZeroHomClass F G₀ M₀]
  [MonoidWithZeroHomClass F' G₀ M₀'] (f : F) {a : G₀}

include M₀

theorem map_ne_zero : f a ≠ 0 ↔ a ≠ 0 :=
  ⟨fun hfa ha => hfa <| ha.symm ▸ map_zero f, fun ha => ((IsUnit.mk0 a ha).map f).NeZero⟩

@[simp]
theorem map_eq_zero : f a = 0 ↔ a = 0 :=
  not_iff_not.1 (map_ne_zero f)

omit M₀

include M₀'

theorem eq_on_inv₀ (f g : F') (h : f a = g a) : f a⁻¹ = g a⁻¹ := by
  rcases eq_or_ne a 0 with (rfl | ha)
  · rw [inv_zero, map_zero, map_zero]
    
  · exact (IsUnit.mk0 a ha).eq_on_inv f g h
    

end MonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] [GroupWithZero G₀'] [MonoidWithZeroHomClass F G₀ G₀'] (f : F) (a b : G₀)

include G₀'

/-- A monoid homomorphism between groups with zeros sending `0` to `0` sends `a⁻¹` to `(f a)⁻¹`. -/
@[simp]
theorem map_inv₀ : f a⁻¹ = (f a)⁻¹ := by
  by_cases h:a = 0
  · simp [h]
    
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel h, map_one]

@[simp]
theorem map_div₀ : f (a / b) = f a / f b :=
  map_div' f (map_inv₀ f) a b

@[simp]
theorem coe_inv₀ [HasLiftT G₀ G₀'] [CoeIsMonoidWithZeroHom G₀ G₀'] (a : G₀) : ↑a⁻¹ = (↑a : G₀')⁻¹ :=
  map_inv₀ (MonoidWithZeroHom.coe G₀ G₀') a

@[simp]
theorem coe_div₀ [HasLiftT G₀ G₀'] [CoeIsMonoidWithZeroHom G₀ G₀'] (a b : G₀) : ↑(a / b) = (↑a : G₀') / ↑b :=
  map_div₀ (MonoidWithZeroHom.coe G₀ G₀') a b

end GroupWithZero

/-- We define the inverse as a `monoid_with_zero_hom` by extending the inverse map by zero
on non-units. -/
noncomputable def MonoidWithZero.inverse {M : Type _} [CommMonoidWithZero M] : M →*₀ M where
  toFun := Ring.inverse
  map_zero' := Ring.inverse_zero _
  map_one' := Ring.inverse_one _
  map_mul' x y := (Ring.mul_inverse_rev x y).trans (mul_comm _ _)

@[simp]
theorem MonoidWithZero.coe_inverse {M : Type _} [CommMonoidWithZero M] :
    (MonoidWithZero.inverse : M → M) = Ring.inverse :=
  rfl

@[simp]
theorem MonoidWithZero.inverse_apply {M : Type _} [CommMonoidWithZero M] (a : M) :
    MonoidWithZero.inverse a = Ring.inverse a :=
  rfl

/-- Inversion on a commutative group with zero, considered as a monoid with zero homomorphism. -/
def invMonoidWithZeroHom {G₀ : Type _} [CommGroupWithZero G₀] : G₀ →*₀ G₀ :=
  { invMonoidHom with map_zero' := inv_zero }

section NoncomputableDefs

open Classical

variable {M : Type _} [Nontrivial M]

/-- Constructs a `group_with_zero` structure on a `monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def groupWithZeroOfIsUnitOrEqZero [hM : MonoidWithZero M] (h : ∀ a : M, IsUnit a ∨ a = 0) :
    GroupWithZero M :=
  { hM with inv := fun a => if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹, inv_zero := dif_pos rfl,
    mul_inv_cancel := fun a h0 => by
      change (a * if h0 : a = 0 then 0 else ↑((h a).resolve_right h0).Unit⁻¹) = 1
      rw [dif_neg h0, Units.mul_inv_eq_iff_eq_mul, one_mul, IsUnit.unit_spec],
    exists_pair_ne := Nontrivial.exists_pair_ne }

/-- Constructs a `comm_group_with_zero` structure on a `comm_monoid_with_zero`
  consisting only of units and 0. -/
noncomputable def commGroupWithZeroOfIsUnitOrEqZero [hM : CommMonoidWithZero M] (h : ∀ a : M, IsUnit a ∨ a = 0) :
    CommGroupWithZero M :=
  { groupWithZeroOfIsUnitOrEqZero h, hM with }

end NoncomputableDefs

