/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Group.Defs
import Mathbin.Logic.Nontrivial
import Mathbin.Algebra.NeZero

/-!
# Typeclasses for groups with an adjoined zero element

This file provides just the typeclass definitions, and the projection lemmas that expose their
members.

## Main definitions

* `group_with_zero`
* `comm_group_with_zero`
-/


universe u

-- We have to fix the universe of `G₀` here, since the default argument to
-- `group_with_zero.div'` cannot contain a universe metavariable.
variable {G₀ : Type u} {M₀ M₀' G₀' : Type _}

#print MulZeroClass /-
/-- Typeclass for expressing that a type `M₀` with multiplication and a zero satisfies
`0 * a = 0` and `a * 0 = 0` for all `a : M₀`. -/
@[protect_proj]
class MulZeroClass (M₀ : Type _) extends Mul M₀, Zero M₀ where
  zero_mul : ∀ a : M₀, 0 * a = 0
  mul_zero : ∀ a : M₀, a * 0 = 0
#align mul_zero_class MulZeroClass
-/

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

@[ematch, simp]
theorem zero_mul (a : M₀) : 0 * a = 0 :=
  MulZeroClass.zero_mul a
#align zero_mul zero_mul

@[ematch, simp]
theorem mul_zero (a : M₀) : a * 0 = 0 :=
  MulZeroClass.mul_zero a
#align mul_zero mul_zero

end MulZeroClass

/-- Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`
for all `a` and `b` of type `G₀`. -/
class NoZeroDivisors (M₀ : Type _) [Mul M₀] [Zero M₀] : Prop where
  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0
#align no_zero_divisors NoZeroDivisors

export NoZeroDivisors (eq_zero_or_eq_zero_of_mul_eq_zero)

#print SemigroupWithZero /-
/-- A type `S₀` is a "semigroup with zero” if it is a semigroup with zero element, and `0` is left
and right absorbing. -/
@[protect_proj]
class SemigroupWithZero (S₀ : Type _) extends Semigroup S₀, MulZeroClass S₀
#align semigroup_with_zero SemigroupWithZero
-/

#print MulZeroOneClass /-
/- By defining this _after_ `semigroup_with_zero`, we ensure that searches for `mul_zero_class` find
this class first. -/
/-- A typeclass for non-associative monoids with zero elements. -/
@[protect_proj]
class MulZeroOneClass (M₀ : Type _) extends MulOneClass M₀, MulZeroClass M₀
#align mul_zero_one_class MulZeroOneClass
-/

#print MonoidWithZero /-
/-- A type `M₀` is a “monoid with zero” if it is a monoid with zero element, and `0` is left
and right absorbing. -/
@[protect_proj]
class MonoidWithZero (M₀ : Type _) extends Monoid M₀, MulZeroOneClass M₀
#align monoid_with_zero MonoidWithZero
-/

#print MonoidWithZero.toSemigroupWithZero /-
-- see Note [lower instance priority]
instance (priority := 100) MonoidWithZero.toSemigroupWithZero (M₀ : Type _) [MonoidWithZero M₀] :
    SemigroupWithZero M₀ :=
  { ‹MonoidWithZero M₀› with }
#align monoid_with_zero.to_semigroup_with_zero MonoidWithZero.toSemigroupWithZero
-/

/-- A type `M` is a `cancel_monoid_with_zero` if it is a monoid with zero element, `0` is left
and right absorbing, and left/right multiplication by a non-zero element is injective. -/
@[protect_proj]
class CancelMonoidWithZero (M₀ : Type _) extends MonoidWithZero M₀ where
  mul_left_cancel_of_ne_zero : ∀ {a b c : M₀}, a ≠ 0 → a * b = a * c → b = c
  mul_right_cancel_of_ne_zero : ∀ {a b c : M₀}, b ≠ 0 → a * b = c * b → a = c
#align cancel_monoid_with_zero CancelMonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

theorem mul_left_cancel₀ (ha : a ≠ 0) (h : a * b = a * c) : b = c :=
  CancelMonoidWithZero.mul_left_cancel_of_ne_zero ha h
#align mul_left_cancel₀ mul_left_cancel₀

theorem mul_right_cancel₀ (hb : b ≠ 0) (h : a * b = c * b) : a = c :=
  CancelMonoidWithZero.mul_right_cancel_of_ne_zero hb h
#align mul_right_cancel₀ mul_right_cancel₀

theorem mul_right_injective₀ (ha : a ≠ 0) : Function.Injective ((· * ·) a) := fun b c => mul_left_cancel₀ ha
#align mul_right_injective₀ mul_right_injective₀

theorem mul_left_injective₀ (hb : b ≠ 0) : Function.Injective fun a => a * b := fun a c => mul_right_cancel₀ hb
#align mul_left_injective₀ mul_left_injective₀

end CancelMonoidWithZero

/-- A type `M` is a commutative “monoid with zero” if it is a commutative monoid with zero
element, and `0` is left and right absorbing. -/
@[protect_proj]
class CommMonoidWithZero (M₀ : Type _) extends CommMonoid M₀, MonoidWithZero M₀
#align comm_monoid_with_zero CommMonoidWithZero

/-- A type `M` is a `cancel_comm_monoid_with_zero` if it is a commutative monoid with zero element,
 `0` is left and right absorbing,
  and left/right multiplication by a non-zero element is injective. -/
@[protect_proj]
class CancelCommMonoidWithZero (M₀ : Type _) extends CommMonoidWithZero M₀, CancelMonoidWithZero M₀
#align cancel_comm_monoid_with_zero CancelCommMonoidWithZero

#print GroupWithZero /-
/-- A type `G₀` is a “group with zero” if it is a monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`.

Examples include division rings and the ordered monoids that are the
target of valuations in general valuation theory.-/
class GroupWithZero (G₀ : Type u) extends MonoidWithZero G₀, DivInvMonoid G₀, Nontrivial G₀ where
  inv_zero : (0 : G₀)⁻¹ = 0
  mul_inv_cancel : ∀ a : G₀, a ≠ 0 → a * a⁻¹ = 1
#align group_with_zero GroupWithZero
-/

section GroupWithZero

variable [GroupWithZero G₀]

@[simp]
theorem inv_zero : (0 : G₀)⁻¹ = 0 :=
  GroupWithZero.inv_zero
#align inv_zero inv_zero

@[simp]
theorem mul_inv_cancel {a : G₀} (h : a ≠ 0) : a * a⁻¹ = 1 :=
  GroupWithZero.mul_inv_cancel a h
#align mul_inv_cancel mul_inv_cancel

end GroupWithZero

/-- A type `G₀` is a commutative “group with zero”
if it is a commutative monoid with zero element (distinct from `1`)
such that every nonzero element is invertible.
The type is required to come with an “inverse” function, and the inverse of `0` must be `0`. -/
class CommGroupWithZero (G₀ : Type _) extends CommMonoidWithZero G₀, GroupWithZero G₀
#align comm_group_with_zero CommGroupWithZero

section NeZero

variable [MulZeroOneClass M₀] [Nontrivial M₀] {a b : M₀}

/-- In a nontrivial monoid with zero, zero and one are different. -/
@[simp]
theorem zero_ne_one : 0 ≠ (1 : M₀) := by
  intro h
  rcases exists_pair_ne M₀ with ⟨x, y, hx⟩
  apply hx
  calc
    x = 1 * x := by rw [one_mul]
    _ = 0 := by rw [← h, zero_mul]
    _ = 1 * y := by rw [← h, zero_mul]
    _ = y := by rw [one_mul]
    
#align zero_ne_one zero_ne_one

@[simp]
theorem one_ne_zero : (1 : M₀) ≠ 0 :=
  zero_ne_one.symm
#align one_ne_zero one_ne_zero

instance NeZero.one (R) [MulZeroOneClass R] [Nontrivial R] : NeZero (1 : R) :=
  ⟨one_ne_zero⟩
#align ne_zero.one NeZero.one

theorem ne_zero_of_eq_one {a : M₀} (h : a = 1) : a ≠ 0 :=
  calc
    a = 1 := h
    _ ≠ 0 := one_ne_zero
    
#align ne_zero_of_eq_one ne_zero_of_eq_one

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) : Nontrivial M₀' :=
  ⟨⟨0, 1,
      mt (congr_arg f) <| by
        rw [zero, one]
        exact zero_ne_one⟩⟩
#align pullback_nonzero pullback_nonzero

end NeZero

section MulZeroClass

variable [MulZeroClass M₀]

theorem mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) : a * b = 0 :=
  h.symm ▸ zero_mul b
#align mul_eq_zero_of_left mul_eq_zero_of_left

theorem mul_eq_zero_of_right (a : M₀) {b : M₀} (h : b = 0) : a * b = 0 :=
  h.symm ▸ mul_zero a
#align mul_eq_zero_of_right mul_eq_zero_of_right

variable [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩
#align mul_eq_zero mul_eq_zero

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]
#align zero_eq_mul zero_eq_mul

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  mul_eq_zero.Not.trans not_or
#align mul_ne_zero_iff mul_ne_zero_iff

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| (or_comm' _ _).trans mul_eq_zero.symm
#align mul_eq_zero_comm mul_eq_zero_comm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
  mul_eq_zero_comm.Not
#align mul_ne_zero_comm mul_ne_zero_comm

theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp
#align mul_self_eq_zero mul_self_eq_zero

theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp
#align zero_eq_mul_self zero_eq_mul_self

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 :=
  mul_self_eq_zero.Not
#align mul_self_ne_zero mul_self_ne_zero

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 :=
  zero_eq_mul_self.Not
#align zero_ne_mul_self zero_ne_mul_self

end MulZeroClass

