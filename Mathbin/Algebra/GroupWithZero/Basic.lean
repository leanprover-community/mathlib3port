/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Algebra.Group.InjSurj
import Mathbin.Algebra.GroupWithZero.Defs
import Mathbin.Algebra.Group.OrderSynonym

/-!
# Groups with an adjoined zero element

This file describes structures that are not usually studied on their own right in mathematics,
namely a special sort of monoid: apart from a distinguished “zero element” they form a group,
or in other words, they are groups with an adjoined zero element.

Examples are:

* division rings;
* the value monoid of a multiplicative valuation;
* in particular, the non-negative real numbers.

## Main definitions

Various lemmas about `group_with_zero` and `comm_group_with_zero`.
To reduce import dependencies, the type-classes themselves are in
`algebra.group_with_zero.defs`.

## Implementation details

As is usual in mathlib, we extend the inverse function to the zero element,
and require `0⁻¹ = 0`.

-/


open Classical

open Function

variable {α M₀ G₀ M₀' G₀' F F' : Type _}

section

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]

/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]

theorem mul_eq_zero_of_left (h : a = 0) (b : M₀) : a * b = 0 :=
  h.symm ▸ zero_mul b

theorem mul_eq_zero_of_right (a : M₀) (h : b = 0) : a * b = 0 :=
  h.symm ▸ mul_zero a

theorem left_ne_zero_of_mul : a * b ≠ 0 → a ≠ 0 :=
  mt fun h => mul_eq_zero_of_left h b

theorem right_ne_zero_of_mul : a * b ≠ 0 → b ≠ 0 :=
  mt (mul_eq_zero_of_right a)

theorem ne_zero_and_ne_zero_of_mul (h : a * b ≠ 0) : a ≠ 0 ∧ b ≠ 0 :=
  ⟨left_ne_zero_of_mul h, right_ne_zero_of_mul h⟩

theorem mul_eq_zero_of_ne_zero_imp_eq_zero {a b : M₀} (h : a ≠ 0 → b = 0) : a * b = 0 :=
  if ha : a = 0 then by rw [ha, zero_mul] else by rw [h ha, mul_zero]

/-- To match `one_mul_eq_id`. -/
theorem zero_mul_eq_const : (· * ·) (0 : M₀) = Function.const _ 0 :=
  funext zero_mul

/-- To match `mul_one_eq_id`. -/
theorem mul_zero_eq_const : (· * (0 : M₀)) = Function.const _ 0 :=
  funext mul_zero

end MulZeroClass

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected theorem Function.Injective.no_zero_divisors [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀'] [NoZeroDivisors M₀']
    (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : NoZeroDivisors M₀ :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun x y H =>
      have : f x * f y = 0 := by rw [← mul, H, zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (fun H => hf <| by rwa [zero]) fun H => hf <| by rwa [zero] }

section Mul

variable [Mul M₀] [Zero M₀] [NoZeroDivisors M₀] {a b : M₀}

theorem eq_zero_of_mul_self_eq_zero (h : a * a = 0) : a = 0 :=
  (eq_zero_or_eq_zero_of_mul_eq_zero h).elim id id

@[field_simps]
theorem mul_ne_zero (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
  mt eq_zero_or_eq_zero_of_mul_eq_zero <| not_or.mpr ⟨ha, hb⟩

end Mul

section

variable [MulZeroClass M₀] [NoZeroDivisors M₀] {a b : M₀}

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0 :=
  ⟨eq_zero_or_eq_zero_of_mul_eq_zero, fun o => o.elim (fun h => mul_eq_zero_of_left h b) (mul_eq_zero_of_right a)⟩

/-- If `α` has no zero divisors, then the product of two elements equals zero iff one of them
equals zero. -/
@[simp]
theorem zero_eq_mul : 0 = a * b ↔ a = 0 ∨ b = 0 := by rw [eq_comm, mul_eq_zero]

/-- If `α` has no zero divisors, then the product of two elements is nonzero iff both of them
are nonzero. -/
theorem mul_ne_zero_iff : a * b ≠ 0 ↔ a ≠ 0 ∧ b ≠ 0 :=
  mul_eq_zero.Not.trans not_or

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` equals zero iff so is
`b * a`. -/
theorem mul_eq_zero_comm : a * b = 0 ↔ b * a = 0 :=
  mul_eq_zero.trans <| (or_comm' _ _).trans mul_eq_zero.symm

/-- If `α` has no zero divisors, then for elements `a, b : α`, `a * b` is nonzero iff so is
`b * a`. -/
theorem mul_ne_zero_comm : a * b ≠ 0 ↔ b * a ≠ 0 :=
  mul_eq_zero_comm.Not

theorem mul_self_eq_zero : a * a = 0 ↔ a = 0 := by simp

theorem zero_eq_mul_self : 0 = a * a ↔ a = 0 := by simp

theorem mul_self_ne_zero : a * a ≠ 0 ↔ a ≠ 0 :=
  mul_self_eq_zero.Not

theorem zero_ne_mul_self : 0 ≠ a * a ↔ a ≠ 0 :=
  zero_eq_mul_self.Not

end

end

section

variable [MulZeroOneClass M₀]

/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }

/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }

/-- In a monoid with zero, if zero equals one, then zero is the only element. -/
theorem eq_zero_of_zero_eq_one (h : (0 : M₀) = 1) (a : M₀) : a = 0 := by rw [← mul_one a, ← h, mul_zero]

/-- In a monoid with zero, if zero equals one, then zero is the unique element.

Somewhat arbitrarily, we define the default element to be `0`.
All other elements will be provably equal to it, but not necessarily definitionally equal. -/
def uniqueOfZeroEqOne (h : (0 : M₀) = 1) : Unique M₀ where
  default := 0
  uniq := eq_zero_of_zero_eq_one h

/-- In a monoid with zero, zero equals one if and only if all elements of that semiring
are equal. -/
theorem subsingleton_iff_zero_eq_one : (0 : M₀) = 1 ↔ Subsingleton M₀ :=
  ⟨fun h => @Unique.subsingleton _ (uniqueOfZeroEqOne h), fun h => @Subsingleton.elim _ h _ _⟩

alias subsingleton_iff_zero_eq_one ↔ subsingleton_of_zero_eq_one _

theorem eq_of_zero_eq_one (h : (0 : M₀) = 1) (a b : M₀) : a = b :=
  @Subsingleton.elim _ (subsingleton_of_zero_eq_one h) a b

/-- In a monoid with zero, either zero and one are nonequal, or zero is the only element. -/
theorem zero_ne_one_or_forall_eq_0 : (0 : M₀) ≠ 1 ∨ ∀ a : M₀, a = 0 :=
  not_or_of_imp eq_zero_of_zero_eq_one

end

section

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
    

@[simp]
theorem one_ne_zero : (1 : M₀) ≠ 0 :=
  zero_ne_one.symm

theorem ne_zero_of_eq_one {a : M₀} (h : a = 1) : a ≠ 0 :=
  calc
    a = 1 := h
    _ ≠ 0 := one_ne_zero
    

theorem left_ne_zero_of_mul_eq_one (h : a * b = 1) : a ≠ 0 :=
  left_ne_zero_of_mul <| ne_zero_of_eq_one h

theorem right_ne_zero_of_mul_eq_one (h : a * b = 1) : b ≠ 0 :=
  right_ne_zero_of_mul <| ne_zero_of_eq_one h

/-- Pullback a `nontrivial` instance along a function sending `0` to `0` and `1` to `1`. -/
protected theorem pullback_nonzero [Zero M₀'] [One M₀'] (f : M₀' → M₀) (zero : f 0 = 0) (one : f 1 = 1) :
    Nontrivial M₀' :=
  ⟨⟨0, 1,
      mt (congr_arg f) <| by
        rw [zero, one]
        exact zero_ne_one⟩⟩

end

section SemigroupWithZero

/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }

/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }

end SemigroupWithZero

section MonoidWithZero

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZero M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

-- see Note [lower instance priority]
instance (priority := 10) CancelMonoidWithZero.to_no_zero_divisors : NoZeroDivisors M₀ :=
  ⟨fun a b ab0 => by
    by_cases a = 0
    · left
      exact h
      
    right
    apply CancelMonoidWithZero.mul_left_cancel_of_ne_zero h
    rw [ab0, mul_zero]⟩

theorem mul_left_inj' (hc : c ≠ 0) : a * c = b * c ↔ a = b :=
  (mul_left_injective₀ hc).eq_iff

theorem mul_right_inj' (ha : a ≠ 0) : a * b = a * c ↔ b = c :=
  (mul_right_injective₀ ha).eq_iff

@[simp]
theorem mul_eq_mul_right_iff : a * c = b * c ↔ a = b ∨ c = 0 := by
  by_cases hc:c = 0 <;> [simp [hc], simp [mul_left_inj', hc]]

@[simp]
theorem mul_eq_mul_left_iff : a * b = a * c ↔ b = c ∨ a = 0 := by
  by_cases ha:a = 0 <;> [simp [ha], simp [mul_right_inj', ha]]

theorem mul_right_eq_self₀ : a * b = a ↔ b = 1 ∨ a = 0 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 ∨ a = 0 := mul_eq_mul_left_iff
    

theorem mul_left_eq_self₀ : a * b = b ↔ a = 1 ∨ b = 0 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 ∨ b = 0 := mul_eq_mul_right_iff
    

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelMonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with
    mul_left_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl,
    mul_right_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl }

/-- An element of a `cancel_monoid_with_zero` fixed by right multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_right (h₁ : b ≠ 1) (h₂ : a * b = a) : a = 0 :=
  Classical.by_contradiction fun ha => h₁ <| mul_left_cancel₀ ha <| h₂.symm ▸ (mul_one a).symm

/-- An element of a `cancel_monoid_with_zero` fixed by left multiplication by an element other
than one must be zero. -/
theorem eq_zero_of_mul_eq_self_left (h₁ : b ≠ 1) (h₂ : b * a = a) : a = 0 :=
  Classical.by_contradiction fun ha => h₁ <| mul_right_cancel₀ ha <| h₂.symm ▸ (one_mul a).symm

end CancelMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀] {a b c : M₀}

/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoidWithZero M₀' :=
  { hf.CommMonoidWithZero f zero one mul npow, hf.CancelMonoidWithZero f zero one mul npow with }

end CancelCommMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow, pullback_nonzero f zero one with
    inv_zero := hf <| by erw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx => hf <| by erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)] }

/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow with
    inv_zero := by erw [← zero, ← inv, inv_zero],
    mul_inv_cancel :=
      hf.forall.2 fun x hx => by
        erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) <| trans_rel_left Ne hx zero.symm)] <;> exact one,
    exists_pair_ne := ⟨0, 1, h01⟩ }

@[simp]
theorem mul_inv_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) := mul_assoc _ _ _
    _ = a := by simp [h]
    

@[simp]
theorem mul_inv_cancel_left₀ (h : a ≠ 0) (b : G₀) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
    

theorem inv_ne_zero (h : a ≠ 0) : a⁻¹ ≠ 0 := fun a_eq_0 => by simpa [a_eq_0] using mul_inv_cancel h

@[simp]
theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  calc
    a⁻¹ * a = a⁻¹ * a * a⁻¹ * a⁻¹⁻¹ := by simp [inv_ne_zero h]
    _ = a⁻¹ * a⁻¹⁻¹ := by simp [h]
    _ = 1 := by simp [inv_ne_zero h]
    

theorem GroupWithZero.mul_left_injective (h : x ≠ 0) : Function.Injective fun y => x * y := fun y y' w => by
  simpa only [← mul_assoc, inv_mul_cancel h, one_mul] using congr_arg (fun y => x⁻¹ * y) w

theorem GroupWithZero.mul_right_injective (h : x ≠ 0) : Function.Injective fun y => y * x := fun y y' w => by
  simpa only [mul_assoc, mul_inv_cancel h, mul_one] using congr_arg (fun y => y * x⁻¹) w

@[simp]
theorem inv_mul_cancel_right₀ (h : b ≠ 0) (a : G₀) : a * b⁻¹ * b = a :=
  calc
    a * b⁻¹ * b = a * (b⁻¹ * b) := mul_assoc _ _ _
    _ = a := by simp [h]
    

@[simp]
theorem inv_mul_cancel_left₀ (h : a ≠ 0) (b : G₀) : a⁻¹ * (a * b) = b :=
  calc
    a⁻¹ * (a * b) = a⁻¹ * a * b := (mul_assoc _ _ _).symm
    _ = b := by simp [h]
    

private theorem inv_eq_of_mul (h : a * b = 1) : a⁻¹ = b := by
  rw [← inv_mul_cancel_left₀ (left_ne_zero_of_mul_eq_one h) b, h, mul_one]

-- See note [lower instance priority]
instance (priority := 100) GroupWithZero.toDivisionMonoid : DivisionMonoid G₀ :=
  { ‹GroupWithZero G₀› with inv := Inv.inv,
    inv_inv := fun a => by
      by_cases h:a = 0
      · simp [h]
        
      · exact left_inv_eq_right_inv (inv_mul_cancel <| inv_ne_zero h) (inv_mul_cancel h)
        ,
    mul_inv_rev := fun a b => by
      by_cases ha:a = 0
      · simp [ha]
        
      by_cases hb:b = 0
      · simp [hb]
        
      refine' inv_eq_of_mul _
      simp [mul_assoc, ha, hb],
    inv_eq_of_mul := fun a b => inv_eq_of_mul }

end GroupWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c : G₀}

@[simp]
theorem zero_div (a : G₀) : 0 / a = 0 := by rw [div_eq_mul_inv, zero_mul]

@[simp]
theorem div_zero (a : G₀) : a / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, mul_zero]

/-- Multiplying `a` by itself and then by its inverse results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_self_mul_inv (a : G₀) : a * a * a⁻¹ = a := by
  by_cases h:a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [mul_assoc, mul_inv_cancel h, mul_one]
    

/-- Multiplying `a` by its inverse and then by itself results in `a`
(whether or not `a` is zero). -/
@[simp]
theorem mul_inv_mul_self (a : G₀) : a * a⁻¹ * a = a := by
  by_cases h:a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [mul_inv_cancel h, one_mul]
    

/-- Multiplying `a⁻¹` by `a` twice results in `a` (whether or not `a`
is zero). -/
@[simp]
theorem inv_mul_mul_self (a : G₀) : a⁻¹ * a * a = a := by
  by_cases h:a = 0
  · rw [h, inv_zero, mul_zero]
    
  · rw [inv_mul_cancel h, one_mul]
    

/-- Multiplying `a` by itself and then dividing by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem mul_self_div_self (a : G₀) : a * a / a = a := by rw [div_eq_mul_inv, mul_self_mul_inv a]

/-- Dividing `a` by itself and then multiplying by itself results in `a`, whether or not `a` is
zero. -/
@[simp]
theorem div_self_mul_self (a : G₀) : a / a * a = a := by rw [div_eq_mul_inv, mul_inv_mul_self a]

attribute [local simp] div_eq_mul_inv mul_comm mul_assoc mul_left_comm

@[simp]
theorem div_self_mul_self' (a : G₀) : a / (a * a) = a⁻¹ :=
  calc
    a / (a * a) = a⁻¹⁻¹ * a⁻¹ * a⁻¹ := by simp [mul_inv_rev]
    _ = a⁻¹ := inv_mul_mul_self _
    

theorem one_div_ne_zero {a : G₀} (h : a ≠ 0) : 1 / a ≠ 0 := by simpa only [one_div] using inv_ne_zero h

@[simp]
theorem inv_eq_zero {a : G₀} : a⁻¹ = 0 ↔ a = 0 := by rw [inv_eq_iff_inv_eq, inv_zero, eq_comm]

@[simp]
theorem zero_eq_inv {a : G₀} : 0 = a⁻¹ ↔ 0 = a :=
  eq_comm.trans <| inv_eq_zero.trans eq_comm

/-- Dividing `a` by the result of dividing `a` by itself results in
`a` (whether or not `a` is zero). -/
@[simp]
theorem div_div_self (a : G₀) : a / (a / a) = a := by
  rw [div_div_eq_mul_div]
  exact mul_self_div_self a

theorem ne_zero_of_one_div_ne_zero {a : G₀} (h : 1 / a ≠ 0) : a ≠ 0 := fun ha : a = 0 => by
  rw [ha, div_zero] at h
  contradiction

theorem eq_zero_of_one_div_eq_zero {a : G₀} (h : 1 / a = 0) : a = 0 :=
  Classical.by_cases (fun ha => ha) fun ha => ((one_div_ne_zero ha) h).elim

theorem mul_left_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => a * g := fun g =>
  ⟨a⁻¹ * g, by simp [← mul_assoc, mul_inv_cancel h]⟩

theorem mul_right_surjective₀ {a : G₀} (h : a ≠ 0) : Surjective fun g => g * a := fun g =>
  ⟨g * a⁻¹, by simp [mul_assoc, inv_mul_cancel h]⟩

end GroupWithZero

section CommGroupWithZero

-- comm
variable [CommGroupWithZero G₀] {a b c d : G₀}

/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero h01 f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }

theorem div_mul_eq_mul_div₀ (a b c : G₀) : a / c * b = a * b / c := by simp_rw [div_eq_mul_inv, mul_assoc, mul_comm c⁻¹]

end CommGroupWithZero

/-! ### Order dual -/


open OrderDual

instance [h : MulZeroClass α] : MulZeroClass αᵒᵈ :=
  h

instance [h : MulZeroOneClass α] : MulZeroOneClass αᵒᵈ :=
  h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors αᵒᵈ :=
  h

instance [h : SemigroupWithZero α] : SemigroupWithZero αᵒᵈ :=
  h

instance [h : MonoidWithZero α] : MonoidWithZero αᵒᵈ :=
  h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero αᵒᵈ :=
  h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero αᵒᵈ :=
  h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero αᵒᵈ :=
  h

instance [h : GroupWithZero α] : GroupWithZero αᵒᵈ :=
  h

instance [h : CommGroupWithZero α] : CommGroupWithZero αᵒᵈ :=
  h

/-! ### Lexicographic order -/


instance [h : MulZeroClass α] : MulZeroClass (Lex α) :=
  h

instance [h : MulZeroOneClass α] : MulZeroOneClass (Lex α) :=
  h

instance [Mul α] [Zero α] [h : NoZeroDivisors α] : NoZeroDivisors (Lex α) :=
  h

instance [h : SemigroupWithZero α] : SemigroupWithZero (Lex α) :=
  h

instance [h : MonoidWithZero α] : MonoidWithZero (Lex α) :=
  h

instance [h : CancelMonoidWithZero α] : CancelMonoidWithZero (Lex α) :=
  h

instance [h : CommMonoidWithZero α] : CommMonoidWithZero (Lex α) :=
  h

instance [h : CancelCommMonoidWithZero α] : CancelCommMonoidWithZero (Lex α) :=
  h

instance [h : GroupWithZero α] : GroupWithZero (Lex α) :=
  h

instance [h : CommGroupWithZero α] : CommGroupWithZero (Lex α) :=
  h

