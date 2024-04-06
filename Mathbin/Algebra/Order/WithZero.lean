/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot
-/
import Algebra.GroupWithZero.Units.Equiv
import Algebra.GroupWithZero.InjSurj
import Algebra.Order.Group.Units
import Algebra.Order.Monoid.Basic
import Algebra.Order.Monoid.WithZero
import Algebra.Order.Group.Instances
import Algebra.Order.Monoid.TypeTags

#align_import algebra.order.with_zero from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.

Note that to avoid issues with import cycles, `linear_ordered_comm_monoid_with_zero` is defined
in another file. However, the lemmas about it are stated here.
-/


#print LinearOrderedCommGroupWithZero /-
/-- A linearly ordered commutative group with a zero element. -/
@[protect_proj]
class LinearOrderedCommGroupWithZero (α : Type _) extends LinearOrderedCommMonoidWithZero α,
    CommGroupWithZero α
#align linear_ordered_comm_group_with_zero LinearOrderedCommGroupWithZero
-/

variable {α : Type _}

variable {a b c d x y z : α}

instance [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.orderedCommMonoid,
    Multiplicative.linearOrder with
    zero := Multiplicative.ofAdd (⊤ : α)
    zero_mul := top_add
    mul_zero := add_top
    zero_le_one := (le_top : (0 : α) ≤ ⊤) }

instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.divInvMonoid, instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual,
    Multiplicative.instNontrivial with
    inv_zero := LinearOrderedAddCommGroupWithTop.neg_top
    mul_inv_cancel := LinearOrderedAddCommGroupWithTop.add_neg_cancel }

instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) :=
  { WithZero.linearOrder,
    WithZero.commMonoidWithZero with
    mul_le_mul_left := fun x y => mul_le_mul_left'
    zero_le_one := WithZero.zero_le _ }

instance [LinearOrderedCommGroup α] : LinearOrderedCommGroupWithZero (WithZero α) :=
  { WithZero.instLinearOrderedCommMonoidWithZero, WithZero.commGroupWithZero with }

section LinearOrderedCommMonoid

variable [LinearOrderedCommMonoidWithZero α]

#print Function.Injective.linearOrderedCommMonoidWithZero /-
/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/
/-- Pullback a `linear_ordered_comm_monoid_with_zero` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.linearOrderedCommMonoidWithZero {β : Type _} [Zero β] [One β] [Mul β]
    [Pow β ℕ] [Sup β] [Inf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoidWithZero β :=
  { LinearOrder.lift f hf hsup hinf, hf.OrderedCommMonoid f one mul npow,
    hf.CommMonoidWithZero f zero one mul npow with
    zero_le_one :=
      show f 0 ≤ f 1 by simp only [zero, one, LinearOrderedCommMonoidWithZero.zero_le_one] }
#align function.injective.linear_ordered_comm_monoid_with_zero Function.Injective.linearOrderedCommMonoidWithZero
-/

#print zero_le' /-
@[simp]
theorem zero_le' : 0 ≤ a := by
  simpa only [MulZeroClass.mul_zero, mul_one] using mul_le_mul_left' zero_le_one a
#align zero_le' zero_le'
-/

#print not_lt_zero' /-
@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_le zero_le'
#align not_lt_zero' not_lt_zero'
-/

#print le_zero_iff /-
@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h => le_antisymm h zero_le', fun h => h ▸ le_rfl⟩
#align le_zero_iff le_zero_iff
-/

#print zero_lt_iff /-
theorem zero_lt_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gt, fun h => lt_of_le_of_ne zero_le' h.symm⟩
#align zero_lt_iff zero_lt_iff
-/

#print ne_zero_of_lt /-
theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 => not_lt_zero' <| show b < 0 from h1 ▸ h
#align ne_zero_of_lt ne_zero_of_lt
-/

instance : LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) :=
  { Additive.orderedAddCommMonoid,
    Additive.linearOrder with
    top := (0 : α)
    top_add' := fun a => (MulZeroClass.zero_mul a : (0 : α) * a = 0)
    le_top := fun _ => zero_le' }

end LinearOrderedCommMonoid

variable [LinearOrderedCommGroupWithZero α]

#print mul_le_one₀ /-
-- TODO: Do we really need the following two?
/-- Alias of `mul_le_one'` for unification. -/
theorem mul_le_one₀ (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_one' ha hb
#align mul_le_one₀ mul_le_one₀
-/

#print one_le_mul₀ /-
/-- Alias of `one_le_mul'` for unification. -/
theorem one_le_mul₀ (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  one_le_mul ha hb
#align one_le_mul₀ one_le_mul₀
-/

#print le_of_le_mul_right /-
theorem le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b := by
  simpa only [mul_inv_cancel_right₀ h] using mul_le_mul_right' hab c⁻¹
#align le_of_le_mul_right le_of_le_mul_right
-/

#print le_mul_inv_of_mul_le /-
theorem le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
  le_of_le_mul_right h (by simpa [h] using hab)
#align le_mul_inv_of_mul_le le_mul_inv_of_mul_le
-/

#print mul_inv_le_of_le_mul /-
theorem mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b :=
  by
  by_cases h : c = 0
  · simp [h]
  · exact le_of_le_mul_right h (by simpa [h] using hab)
#align mul_inv_le_of_le_mul mul_inv_le_of_le_mul
-/

#print inv_le_one₀ /-
theorem inv_le_one₀ (ha : a ≠ 0) : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  @inv_le_one' _ _ _ _ <| Units.mk0 a ha
#align inv_le_one₀ inv_le_one₀
-/

#print one_le_inv₀ /-
theorem one_le_inv₀ (ha : a ≠ 0) : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  @one_le_inv' _ _ _ _ <| Units.mk0 a ha
#align one_le_inv₀ one_le_inv₀
-/

#print le_mul_inv_iff₀ /-
theorem le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
  ⟨fun h => inv_inv c ▸ mul_inv_le_of_le_mul h, le_mul_inv_of_mul_le hc⟩
#align le_mul_inv_iff₀ le_mul_inv_iff₀
-/

#print mul_inv_le_iff₀ /-
theorem mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
  ⟨fun h => inv_inv c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul⟩
#align mul_inv_le_iff₀ mul_inv_le_iff₀
-/

#print div_le_div₀ /-
theorem div_le_div₀ (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
  if ha : a = 0 then by simp [ha]
  else
    if hc : c = 0 then by simp [inv_ne_zero hb, hc, hd]
    else
      show
        Units.mk0 a ha * (Units.mk0 b hb)⁻¹ ≤ Units.mk0 c hc * (Units.mk0 d hd)⁻¹ ↔
          Units.mk0 a ha * Units.mk0 d hd ≤ Units.mk0 c hc * Units.mk0 b hb
        from mul_inv_le_mul_inv_iff'
#align div_le_div₀ div_le_div₀
-/

#print Units.zero_lt /-
@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 <| u.NeZero
#align units.zero_lt Units.zero_lt
-/

#print mul_lt_mul_of_lt_of_le₀ /-
theorem mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
  have hd : d ≠ 0 := ne_zero_of_lt hcd
  if ha : a = 0 then by rw [ha, MulZeroClass.zero_mul, zero_lt_iff]; exact mul_ne_zero hb hd
  else
    if hc : c = 0 then by rw [hc, MulZeroClass.mul_zero, zero_lt_iff]; exact mul_ne_zero hb hd
    else
      show Units.mk0 a ha * Units.mk0 c hc < Units.mk0 b hb * Units.mk0 d hd from
        mul_lt_mul_of_le_of_lt hab hcd
#align mul_lt_mul_of_lt_of_le₀ mul_lt_mul_of_lt_of_le₀
-/

#print mul_lt_mul₀ /-
theorem mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le₀ hab.le (ne_zero_of_lt hab) hcd
#align mul_lt_mul₀ mul_lt_mul₀
-/

#print mul_inv_lt_of_lt_mul₀ /-
theorem mul_inv_lt_of_lt_mul₀ (h : x < y * z) : x * z⁻¹ < y := by contrapose! h;
  simpa only [inv_inv] using mul_inv_le_of_le_mul h
#align mul_inv_lt_of_lt_mul₀ mul_inv_lt_of_lt_mul₀
-/

#print inv_mul_lt_of_lt_mul₀ /-
theorem inv_mul_lt_of_lt_mul₀ (h : x < y * z) : y⁻¹ * x < z := by rw [mul_comm] at *;
  exact mul_inv_lt_of_lt_mul₀ h
#align inv_mul_lt_of_lt_mul₀ inv_mul_lt_of_lt_mul₀
-/

#print mul_lt_right₀ /-
theorem mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c := by contrapose! h;
  exact le_of_le_mul_right hc h
#align mul_lt_right₀ mul_lt_right₀
-/

#print inv_lt_inv₀ /-
theorem inv_lt_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  show (Units.mk0 a ha)⁻¹ < (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb < Units.mk0 a ha from inv_lt_inv_iff
#align inv_lt_inv₀ inv_lt_inv₀
-/

#print inv_le_inv₀ /-
theorem inv_le_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  show (Units.mk0 a ha)⁻¹ ≤ (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb ≤ Units.mk0 a ha from inv_le_inv_iff
#align inv_le_inv₀ inv_le_inv₀
-/

#print lt_of_mul_lt_mul_of_le₀ /-
theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d :=
  by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  simp_rw [← inv_le_inv₀ ha (ne_of_gt hc)] at hh
  have := mul_lt_mul_of_lt_of_le₀ hh (inv_ne_zero (ne_of_gt hc)) h
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ (ne_of_gt hc)] using this
#align lt_of_mul_lt_mul_of_le₀ lt_of_mul_lt_mul_of_le₀
-/

#print mul_le_mul_right₀ /-
theorem mul_le_mul_right₀ (hc : c ≠ 0) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨le_of_le_mul_right hc, fun hab => mul_le_mul_right' hab _⟩
#align mul_le_mul_right₀ mul_le_mul_right₀
-/

#print mul_le_mul_left₀ /-
theorem mul_le_mul_left₀ (ha : a ≠ 0) : a * b ≤ a * c ↔ b ≤ c := by simp only [mul_comm a];
  exact mul_le_mul_right₀ ha
#align mul_le_mul_left₀ mul_le_mul_left₀
-/

#print div_le_div_right₀ /-
theorem div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]
#align div_le_div_right₀ div_le_div_right₀
-/

#print div_le_div_left₀ /-
theorem div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_left₀ ha, inv_le_inv₀ hb hc]
#align div_le_div_left₀ div_le_div_left₀
-/

#print le_div_iff₀ /-
theorem le_div_iff₀ (hc : c ≠ 0) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]
#align le_div_iff₀ le_div_iff₀
-/

#print div_le_iff₀ /-
theorem div_le_iff₀ (hc : c ≠ 0) : a / c ≤ b ↔ a ≤ b * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]
#align div_le_iff₀ div_le_iff₀
-/

#print OrderIso.mulLeft₀' /-
/-- `equiv.mul_left₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_left₀` refers to the `linear_ordered_field` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulLeft₀ a ha with map_rel_iff' := fun x y => mul_le_mul_left₀ ha }
#align order_iso.mul_left₀' OrderIso.mulLeft₀'
-/

#print OrderIso.mulLeft₀'_symm /-
theorem OrderIso.mulLeft₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulLeft₀' ha).symm = OrderIso.mulLeft₀' (inv_ne_zero ha) := by ext; rfl
#align order_iso.mul_left₀'_symm OrderIso.mulLeft₀'_symm
-/

#print OrderIso.mulRight₀' /-
/-- `equiv.mul_right₀` as an order_iso on a `linear_ordered_comm_group_with_zero.`.

Note that `order_iso.mul_right₀` refers to the `linear_ordered_field` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulRight₀ a ha with map_rel_iff' := fun _ _ => mul_le_mul_right₀ ha }
#align order_iso.mul_right₀' OrderIso.mulRight₀'
-/

#print OrderIso.mulRight₀'_symm /-
theorem OrderIso.mulRight₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulRight₀' ha).symm = OrderIso.mulRight₀' (inv_ne_zero ha) := by ext; rfl
#align order_iso.mul_right₀'_symm OrderIso.mulRight₀'_symm
-/

instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) :=
  { Additive.subNegMonoid, instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual,
    Additive.instNontrivial with
    neg_top := inv_zero
    add_neg_cancel := fun a ha => mul_inv_cancel ha }

