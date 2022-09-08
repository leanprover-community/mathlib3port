/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Anne Baanen
-/
import Mathbin.Algebra.Order.Field

/-!
# Absolute values

This file defines a bundled type of absolute values `absolute_value R S`.

## Main definitions

 * `absolute_value R S` is the type of absolute values on `R` mapping to `S`.
 * `absolute_value.abs` is the "standard" absolute value on `S`, mapping negative `x` to `-x`.
 * `absolute_value.to_monoid_with_zero_hom`: absolute values mapping to a
   linear ordered field preserve `0`, `*` and `1`
 * `is_absolute_value`: a type class stating that `f : β → α` satisfies the axioms of an abs val
-/


/-- `absolute_value R S` is the type of absolute values on `R` mapping to `S`:
the maps that preserve `*`, are nonnegative, positive definite and satisfy the triangle equality. -/
structure AbsoluteValue (R S : Type _) [Semiringₓ R] [OrderedSemiring S] extends R →ₙ* S where
  nonneg' : ∀ x, 0 ≤ to_fun x
  eq_zero' : ∀ x, to_fun x = 0 ↔ x = 0
  add_le' : ∀ x y, to_fun (x + y) ≤ to_fun x + to_fun y

namespace AbsoluteValue

attribute [nolint doc_blame] AbsoluteValue.toMulHom

initialize_simps_projections AbsoluteValue (to_mul_hom_to_fun → apply)

section OrderedSemiring

section Semiringₓ

variable {R S : Type _} [Semiringₓ R] [OrderedSemiring S] (abv : AbsoluteValue R S)

instance mulHomClass : MulHomClass (AbsoluteValue R S) R S where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul := fun f => f.map_mul'

instance : CoeFun (AbsoluteValue R S) fun f => R → S :=
  ⟨fun f => f.toFun⟩

@[simp]
theorem coe_to_mul_hom : ⇑abv.toMulHom = abv :=
  rfl

protected theorem nonneg (x : R) : 0 ≤ abv x :=
  abv.nonneg' x

@[simp]
protected theorem eq_zero {x : R} : abv x = 0 ↔ x = 0 :=
  abv.eq_zero' x

protected theorem add_le (x y : R) : abv (x + y) ≤ abv x + abv y :=
  abv.add_le' x y

@[simp]
protected theorem map_mul (x y : R) : abv (x * y) = abv x * abv y :=
  abv.map_mul' x y

protected theorem pos {x : R} (hx : x ≠ 0) : 0 < abv x :=
  lt_of_le_of_neₓ (abv.Nonneg x) (Ne.symm <| mt abv.eq_zero.mp hx)

@[simp]
protected theorem pos_iff {x : R} : 0 < abv x ↔ x ≠ 0 :=
  ⟨fun h₁ => mt abv.eq_zero.mpr h₁.ne', abv.Pos⟩

protected theorem ne_zero {x : R} (hx : x ≠ 0) : abv x ≠ 0 :=
  (abv.Pos hx).ne'

theorem map_one_of_is_regular (h : IsLeftRegular (abv 1)) : abv 1 = 1 :=
  h <| by
    simp [← abv.map_mul]

@[simp]
protected theorem map_zero : abv 0 = 0 :=
  abv.eq_zero.2 rfl

end Semiringₓ

section Ringₓ

variable {R S : Type _} [Ringₓ R] [OrderedSemiring S] (abv : AbsoluteValue R S)

protected theorem sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assocₓ] using abv.add_le (a - b) (b - c)

@[simp]
theorem map_sub_eq_zero_iff (a b : R) : abv (a - b) = 0 ↔ a = b :=
  abv.eq_zero.trans sub_eq_zero

end Ringₓ

end OrderedSemiring

section OrderedRing

section Semiringₓ

section IsDomain

-- all of these are true for `no_zero_divisors S`; but it doesn't work smoothly with the
-- `is_domain`/`cancel_monoid_with_zero` API
variable {R S : Type _} [Semiringₓ R] [OrderedRing S] (abv : AbsoluteValue R S)

variable [IsDomain S] [Nontrivial R]

@[simp]
protected theorem map_one : abv 1 = 1 :=
  abv.map_one_of_is_regular (is_regular_of_ne_zero <| abv.ne_zero one_ne_zero).left

instance : MonoidWithZeroHomClass (AbsoluteValue R S) R S :=
  { AbsoluteValue.mulHomClass with map_zero := fun f => f.map_zero, map_one := fun f => f.map_one }

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*`, `0` and `1`. -/
def toMonoidWithZeroHom : R →*₀ S :=
  abv

@[simp]
theorem coe_to_monoid_with_zero_hom : ⇑abv.toMonoidWithZeroHom = abv :=
  rfl

/-- Absolute values from a nontrivial `R` to a linear ordered ring preserve `*` and `1`. -/
def toMonoidHom : R →* S :=
  abv

@[simp]
theorem coe_to_monoid_hom : ⇑abv.toMonoidHom = abv :=
  rfl

@[simp]
protected theorem map_pow (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  abv.toMonoidHom.map_pow a n

end IsDomain

end Semiringₓ

section Ringₓ

variable {R S : Type _} [Ringₓ R] [OrderedRing S] (abv : AbsoluteValue R S)

protected theorem le_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  sub_le_iff_le_add.2 <| by
    simpa using abv.add_le (a - b) b

end Ringₓ

end OrderedRing

section OrderedCommRing

variable {R S : Type _} [Ringₓ R] [OrderedCommRing S] (abv : AbsoluteValue R S)

variable [NoZeroDivisors S]

@[simp]
protected theorem map_neg (a : R) : abv (-a) = abv a := by
  by_cases' ha : a = 0
  · simp [ha]
    
  refine'
    (mul_self_eq_mul_self_iff.mp
          (by
            rw [← abv.map_mul, neg_mul_neg, abv.map_mul])).resolve_right
      _
  exact ((neg_lt_zero.mpr (abv.pos ha)).trans (abv.pos (neg_ne_zero.mpr ha))).ne'

protected theorem map_sub (a b : R) : abv (a - b) = abv (b - a) := by
  rw [← neg_sub, abv.map_neg]

end OrderedCommRing

section LinearOrderedRing

variable {R S : Type _} [Semiringₓ R] [LinearOrderedRing S] (abv : AbsoluteValue R S)

/-- `absolute_value.abs` is `abs` as a bundled `absolute_value`. -/
@[simps]
protected def abs : AbsoluteValue S S where
  toFun := abs
  nonneg' := abs_nonneg
  eq_zero' := fun _ => abs_eq_zero
  add_le' := abs_add
  map_mul' := abs_mul

instance : Inhabited (AbsoluteValue S S) :=
  ⟨AbsoluteValue.abs⟩

end LinearOrderedRing

section LinearOrderedCommRing

variable {R S : Type _} [Ringₓ R] [LinearOrderedCommRing S] (abv : AbsoluteValue R S)

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  abs_sub_le_iff.2
    ⟨abv.le_sub _ _, by
      rw [abv.map_sub] <;> apply abv.le_sub⟩

end LinearOrderedCommRing

end AbsoluteValue

-- ./././Mathport/Syntax/Translate/Command.lean:324:30: infer kinds are unsupported in Lean 4: #[`abv_nonneg] []
-- ./././Mathport/Syntax/Translate/Command.lean:324:30: infer kinds are unsupported in Lean 4: #[`abv_eq_zero] []
-- ./././Mathport/Syntax/Translate/Command.lean:324:30: infer kinds are unsupported in Lean 4: #[`abv_add] []
-- ./././Mathport/Syntax/Translate/Command.lean:324:30: infer kinds are unsupported in Lean 4: #[`abv_mul] []
/-- A function `f` is an absolute value if it is nonnegative, zero only at 0, additive, and
multiplicative.

See also the type `absolute_value` which represents a bundled version of absolute values.
-/
class IsAbsoluteValue {S} [OrderedSemiring S] {R} [Semiringₓ R] (f : R → S) : Prop where
  abv_nonneg : ∀ x, 0 ≤ f x
  abv_eq_zero : ∀ {x}, f x = 0 ↔ x = 0
  abv_add : ∀ x y, f (x + y) ≤ f x + f y
  abv_mul : ∀ x y, f (x * y) = f x * f y

namespace IsAbsoluteValue

section OrderedSemiring

variable {S : Type _} [OrderedSemiring S]

variable {R : Type _} [Semiringₓ R] (abv : R → S) [IsAbsoluteValue abv]

/-- A bundled absolute value is an absolute value. -/
instance _root_.absolute_value.is_absolute_value (abv : AbsoluteValue R S) : IsAbsoluteValue abv where
  abv_nonneg := abv.Nonneg
  abv_eq_zero := fun _ => abv.eq_zero
  abv_add := abv.add_le
  abv_mul := abv.map_mul

/-- Convert an unbundled `is_absolute_value` to a bundled `absolute_value`. -/
@[simps]
def toAbsoluteValue : AbsoluteValue R S where
  toFun := abv
  add_le' := abv_add abv
  eq_zero' := fun _ => abv_eq_zero abv
  nonneg' := abv_nonneg abv
  map_mul' := abv_mul abv

theorem abv_zero : abv 0 = 0 :=
  (toAbsoluteValue abv).map_zero

theorem abv_pos {a : R} : 0 < abv a ↔ a ≠ 0 :=
  (toAbsoluteValue abv).pos_iff

end OrderedSemiring

section LinearOrderedRing

variable {S : Type _} [LinearOrderedRing S]

instance abs_is_absolute_value : IsAbsoluteValue (abs : S → S) :=
  AbsoluteValue.abs.IsAbsoluteValue

end LinearOrderedRing

section OrderedRing

variable {S : Type _} [OrderedRing S]

section Semiringₓ

variable {R : Type _} [Semiringₓ R] (abv : R → S) [IsAbsoluteValue abv]

variable [IsDomain S]

theorem abv_one [Nontrivial R] : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one

/-- `abv` as a `monoid_with_zero_hom`. -/
def abvHom [Nontrivial R] : R →*₀ S :=
  (toAbsoluteValue abv).toMonoidWithZeroHom

theorem abv_pow [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv] (a : R) (n : ℕ) : abv (a ^ n) = abv a ^ n :=
  (toAbsoluteValue abv).map_pow a n

end Semiringₓ

section Ringₓ

variable {R : Type _} [Ringₓ R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_sub_le (a b c : R) : abv (a - c) ≤ abv (a - b) + abv (b - c) := by
  simpa [sub_eq_add_neg, add_assocₓ] using abv_add abv (a - b) (b - c)

theorem sub_abv_le_abv_sub (a b : R) : abv a - abv b ≤ abv (a - b) :=
  (toAbsoluteValue abv).le_sub a b

end Ringₓ

end OrderedRing

section OrderedCommRing

variable {S : Type _} [OrderedCommRing S]

section Ringₓ

variable {R : Type _} [Ringₓ R] (abv : R → S) [IsAbsoluteValue abv]

variable [NoZeroDivisors S]

theorem abv_neg (a : R) : abv (-a) = abv a :=
  (toAbsoluteValue abv).map_neg a

theorem abv_sub (a b : R) : abv (a - b) = abv (b - a) :=
  (toAbsoluteValue abv).map_sub a b

end Ringₓ

end OrderedCommRing

section LinearOrderedCommRing

variable {S : Type _} [LinearOrderedCommRing S]

section Ringₓ

variable {R : Type _} [Ringₓ R] (abv : R → S) [IsAbsoluteValue abv]

theorem abs_abv_sub_le_abv_sub (a b : R) : abs (abv a - abv b) ≤ abv (a - b) :=
  (toAbsoluteValue abv).abs_abv_sub_le_abv_sub a b

end Ringₓ

end LinearOrderedCommRing

section LinearOrderedField

variable {S : Type _} [LinearOrderedSemifield S]

section Semiringₓ

variable {R : Type _} [Semiringₓ R] [Nontrivial R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_one' : abv 1 = 1 :=
  (toAbsoluteValue abv).map_one_of_is_regular <|
    (is_regular_of_ne_zero <| (toAbsoluteValue abv).ne_zero one_ne_zero).left

/-- An absolute value as a monoid with zero homomorphism, assuming the target is a semifield. -/
def abvHom' : R →*₀ S :=
  ⟨abv, abv_zero abv, abv_one' abv, abv_mul abv⟩

end Semiringₓ

section DivisionSemiring

variable {R : Type _} [DivisionSemiring R] (abv : R → S) [IsAbsoluteValue abv]

theorem abv_inv (a : R) : abv a⁻¹ = (abv a)⁻¹ :=
  map_inv₀ (abvHom' abv) a

theorem abv_div (a b : R) : abv (a / b) = abv a / abv b :=
  map_div₀ (abvHom' abv) a b

end DivisionSemiring

end LinearOrderedField

end IsAbsoluteValue

