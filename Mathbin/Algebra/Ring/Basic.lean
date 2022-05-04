/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Amelia Livingston, Yury Kudryashov,
Neil Strickland
-/
import Mathbin.Algebra.Divisibility
import Mathbin.Algebra.Regular.Basic
import Mathbin.Data.Pi.Algebra

/-!
# Properties and homomorphisms of semirings and rings

This file proves simple properties of semirings, rings and domains and their unit groups. It also
defines bundled homomorphisms of semirings and rings. As with monoid and groups, we use the same
structure `ring_hom a β`, a.k.a. `α →+* β`, for both homomorphism types.

The unbundled homomorphisms are defined in `deprecated/ring`. They are deprecated and the plan is to
slowly remove them from mathlib.

## Main definitions

ring_hom, nonzero, domain, is_domain

## Notations

* `→+*` for bundled ring homs (also use for semiring homs)
* `→ₙ+*` for bundled non-unital ring homs (also use for non-unital semiring homs)

## Implementation notes

* There's a coercion from bundled homs to fun, and the canonical notation is to
  use the bundled hom as a function via this coercion.

* There is no `semiring_hom` -- the idea is that `ring_hom` is used.
  The constructor for a `ring_hom` between semirings needs a proof of `map_zero`,
  `map_one` and `map_add` as well as `map_mul`; a separate constructor
  `ring_hom.mk'` will construct ring homs between rings from monoid homs given
  only a proof that addition is preserved.

* To avoid repeating lemmas for `units`, this introduces a `has_distrib_neg` typeclass
  which both `R` and `units R` satisfy.

## Tags

`ring_hom`, `semiring_hom`, `semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`,
`is_domain`, `nonzero`, `units`
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `distrib` class
-/


/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj, ancestor Mul Add]
class Distribₓ (R : Type _) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

theorem left_distrib [Distribₓ R] (a b c : R) : a * (b + c) = a * b + a * c :=
  Distribₓ.left_distrib a b c

alias left_distrib ← mul_addₓ

theorem right_distrib [Distribₓ R] (a b c : R) : (a + b) * c = a * c + b * c :=
  Distribₓ.right_distrib a b c

alias right_distrib ← add_mulₓ

theorem distrib_three_right [Distribₓ R] (a b c d : R) : (a + b + c) * d = a * d + b * d + c * d := by
  simp [right_distrib]

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distribₓ S] (f : R → S) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distribₓ R where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := fun x y z =>
    hf <| by
      simp only [*, left_distrib]
  right_distrib := fun x y z =>
    hf <| by
      simp only [*, right_distrib]

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distrib {S} [Distribₓ R] [Add S] [Mul S] (f : R → S) (hf : Surjective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distribₓ S where
  mul := (· * ·)
  add := (· + ·)
  left_distrib :=
    hf.forall₃.2 fun x y z => by
      simp only [← add, ← mul, left_distrib]
  right_distrib :=
    hf.forall₃.2 fun x y z => by
      simp only [← add, ← mul, right_distrib]

/-!
### Semirings
-/


/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj, ancestor AddCommMonoidₓ Distribₓ MulZeroClassₓ]
class NonUnitalNonAssocSemiringₓ (α : Type u) extends AddCommMonoidₓ α, Distribₓ α, MulZeroClassₓ α

/-- An associative but not-necessarily unital semiring. -/
@[protect_proj, ancestor NonUnitalNonAssocSemiringₓ SemigroupWithZeroₓ]
class NonUnitalSemiringₓ (α : Type u) extends NonUnitalNonAssocSemiringₓ α, SemigroupWithZeroₓ α

/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj, ancestor NonUnitalNonAssocSemiringₓ MulZeroOneClassₓ]
class NonAssocSemiringₓ (α : Type u) extends NonUnitalNonAssocSemiringₓ α, MulZeroOneClassₓ α

/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj, ancestor NonUnitalSemiringₓ NonAssocSemiringₓ MonoidWithZeroₓ]
class Semiringₓ (α : Type u) extends NonUnitalSemiringₓ α, NonAssocSemiringₓ α, MonoidWithZeroₓ α

section InjectiveSurjectiveMaps

variable [Zero β] [Add β] [Mul β] [HasScalar ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiringₓ α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalNonAssocSemiringₓ β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiringₓ α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiringₓ α] [One β] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonAssocSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.MulOneClass f one mul with }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semiring {α : Type u} [Semiringₓ α] [One β] [Pow β ℕ] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Semiringₓ β :=
  { hf.MonoidWithZero f zero one mul npow, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiringₓ α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalNonAssocSemiringₓ β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalSemiring {α : Type u} [NonUnitalSemiringₓ α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocSemiring {α : Type u} [NonAssocSemiringₓ α] [One β] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonAssocSemiringₓ β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.MulOneClass f one mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semiring {α : Type u} [Semiringₓ α] [One β] [Pow β ℕ] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Semiringₓ β :=
  { hf.MonoidWithZero f zero one mul npow, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

end InjectiveSurjectiveMaps

section HasOneHasAdd

variable [One α] [Add α]

theorem one_add_one_eq_two : 1 + 1 = (2 : α) := by
  unfold bit0

end HasOneHasAdd

section NonUnitalSemiringₓ

variable [NonUnitalSemiringₓ α]

theorem dvd_add {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd =>
    Dvd.elim h₂ fun e he =>
      Dvd.intro (d + e)
        (by
          simp [left_distrib, hd, he])

end NonUnitalSemiringₓ

section NonAssocSemiringₓ

variable [NonAssocSemiringₓ α]

theorem add_one_mul (a b : α) : (a + 1) * b = a * b + b := by
  rw [add_mulₓ, one_mulₓ]

theorem mul_add_one (a b : α) : a * (b + 1) = a * b + a := by
  rw [mul_addₓ, mul_oneₓ]

theorem one_add_mul (a b : α) : (1 + a) * b = b + a * b := by
  rw [add_mulₓ, one_mulₓ]

theorem mul_one_add (a b : α) : a * (1 + b) = a + a * b := by
  rw [mul_addₓ, mul_oneₓ]

theorem two_mul (n : α) : 2 * n = n + n :=
  Eq.trans (right_distrib 1 1 n)
    (by
      simp )

theorem bit0_eq_two_mul (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm

theorem mul_two (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans
    (by
      simp )

end NonAssocSemiringₓ

section Semiringₓ

variable [Semiringₓ α]

@[to_additive]
theorem mul_ite {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (a * if P then b else c) = if P then a * b else a * c := by
  split_ifs <;> rfl

@[to_additive]
theorem ite_mul {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (if P then a else b) * c = if P then a * c else b * c := by
  split_ifs <;> rfl

-- We make `mul_ite` and `ite_mul` simp lemmas,
-- but not `add_ite` or `ite_add`.
-- The problem we're trying to avoid is dealing with
-- summations of the form `∑ x in s, (f x + ite P 1 0)`,
-- in which `add_ite` followed by `sum_ite` would needlessly slice up
-- the `f x` terms according to whether `P` holds at `x`.
-- There doesn't appear to be a corresponding difficulty so far with
-- `mul_ite` and `ite_mul`.
attribute [simp] mul_ite ite_mul

@[simp]
theorem mul_boole {α} [MulZeroOneClassₓ α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by
  simp

@[simp]
theorem boole_mul {α} [MulZeroOneClassₓ α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by
  simp

theorem ite_mul_zero_left {α : Type _} [MulZeroClassₓ α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = ite P a 0 * b := by
  by_cases' h : P <;> simp [h]

theorem ite_mul_zero_right {α : Type _} [MulZeroClassₓ α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = a * ite P b 0 := by
  by_cases' h : P <;> simp [h]

theorem ite_and_mul_zero {α : Type _} [MulZeroClassₓ α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
    ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm]

end Semiringₓ

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distribₓ R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_addₓ r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distribₓ R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mulₓ _ _ r⟩

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [AddHomClass F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _

end AddHomClass

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : R →+ R where
  toFun := (· * ·) r
  map_zero' := mul_zero r
  map_add' := mul_addₓ r

@[simp]
theorem coe_mul_left {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : ⇑(mulLeft r) = (· * ·) r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : R →+ R where
  toFun := fun a => a * r
  map_zero' := zero_mul r
  map_add' := fun _ _ => add_mulₓ _ _ r

@[simp]
theorem coe_mul_right {R : Type _} [NonUnitalNonAssocSemiringₓ R] (r : R) : ⇑(mulRight r) = (· * r) :=
  rfl

theorem mul_right_apply {R : Type _} [NonUnitalNonAssocSemiringₓ R] (a r : R) : mulRight r a = a * r :=
  rfl

end AddMonoidHom

/-- Bundled non-unital semiring homomorphisms `R →ₙ+* S`; use this for bundled non-unital ring
homomorphisms too.

When possible, instead of parametrizing results over `(f : R →ₙ+* S)`,
you should parametrize over `(F : Type*) [non_unital_ring_hom_class F R S] (f : F)`.

When you extend this structure, make sure to extend `non_unital_ring_hom_class`. -/
structure NonUnitalRingHom (R : Type _) (S : Type _) [NonUnitalNonAssocSemiringₓ R]
  [NonUnitalNonAssocSemiringₓ S] extends R →ₙ* S, R →+ S

-- mathport name: «expr →ₙ+* »
infixr:25 " →ₙ+* " => NonUnitalRingHom

/-- Reinterpret a non-unital ring homomorphism `f : R →ₙ+* S` as a semigroup
homomorphism `R →ₙ* S`. The `simp`-normal form is `(f : R →ₙ* S)`. -/
add_decl_doc NonUnitalRingHom.toMulHom

/-- Reinterpret a non-unital ring homomorphism `f : R →ₙ+* S` as an additive
monoid homomorphism `R →+ S`. The `simp`-normal form is `(f : R →+ S)`. -/
add_decl_doc NonUnitalRingHom.toAddMonoidHom

section NonUnitalRingHomClass

/-- `non_unital_ring_hom_class F R S` states that `F` is a type of non-unital (semi)ring
homomorphisms. You should extend this class when you extend `non_unital_ring_hom`. -/
class NonUnitalRingHomClass (F : Type _) (R S : outParam (Type _)) [NonUnitalNonAssocSemiringₓ R]
  [NonUnitalNonAssocSemiringₓ S] extends MulHomClass F R S, AddMonoidHomClass F R S

variable {F : Type _} [NonUnitalNonAssocSemiringₓ α] [NonUnitalNonAssocSemiringₓ β] [NonUnitalRingHomClass F α β]

instance : CoeTₓ F (α →ₙ+* β) :=
  ⟨fun f => { toFun := f, map_zero' := map_zero f, map_mul' := map_mul f, map_add' := map_add f }⟩

end NonUnitalRingHomClass

namespace NonUnitalRingHom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/


variable {rα : NonUnitalNonAssocSemiringₓ α} {rβ : NonUnitalNonAssocSemiringₓ β}

include rα rβ

instance : NonUnitalRingHomClass (α →ₙ+* β) α β where
  coe := NonUnitalRingHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_add := NonUnitalRingHom.map_add'
  map_zero := NonUnitalRingHom.map_zero'
  map_mul := NonUnitalRingHom.map_mul'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (α →ₙ+* β) fun _ => α → β :=
  ⟨NonUnitalRingHom.toFun⟩

@[simp]
theorem to_fun_eq_coe (f : α →ₙ+* β) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : α → β) h₁ h₂ h₃ : ⇑(⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) = f :=
  rfl

@[simp]
theorem coe_coe {F : Type _} [NonUnitalRingHomClass F α β] (f : F) : ((f : α →ₙ+* β) : α → β) = f :=
  rfl

@[simp]
theorem coe_to_mul_hom (f : α →ₙ+* β) : ⇑f.toMulHom = f :=
  rfl

@[simp]
theorem coe_mul_hom_mk (f : α → β) h₁ h₂ h₃ : ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →ₙ* β) = ⟨f, h₁⟩ :=
  rfl

@[simp]
theorem coe_to_add_monoid_hom (f : α →ₙ+* β) : ⇑f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_add_monoid_hom_mk (f : α → β) h₁ h₂ h₃ : ((⟨f, h₁, h₂, h₃⟩ : α →ₙ+* β) : α →+ β) = ⟨f, h₂, h₃⟩ :=
  rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →ₙ+* β) (f' : α → β) (h : f' = f) : α →ₙ+* β :=
  { f.toMulHom.copy f' h, f.toAddMonoidHom.copy f' h with }

end coe

variable [rα : NonUnitalNonAssocSemiringₓ α] [rβ : NonUnitalNonAssocSemiringₓ β]

section

include rα rβ

variable (f : α →ₙ+* β) {x y : α} {rα rβ}

@[ext]
theorem ext ⦃f g : α →ₙ+* β⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

theorem ext_iff {f g : α →ₙ+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe (f : α →ₙ+* β) h₁ h₂ h₃ : NonUnitalRingHom.mk f h₁ h₂ h₃ = f :=
  ext fun _ => rfl

theorem coe_add_monoid_hom_injective : Function.Injective (coe : (α →ₙ+* β) → α →+ β) := fun f g h =>
  ext fun x => AddMonoidHom.congr_fun h x

theorem coe_mul_hom_injective : Function.Injective (coe : (α →ₙ+* β) → α →ₙ* β) := fun f g h =>
  ext fun x => MulHom.congr_fun h x

end

/-- The identity non-unital ring homomorphism from a non-unital semiring to itself. -/
protected def id (α : Type _) [NonUnitalNonAssocSemiringₓ α] : α →ₙ+* α := by
  refine' { toFun := id, .. } <;> intros <;> rfl

include rα rβ

instance : Zero (α →ₙ+* β) :=
  Zero.mk
    { toFun := 0, map_mul' := fun x y => (mul_zero (0 : β)).symm, map_zero' := rfl,
      map_add' := fun x y => (add_zeroₓ (0 : β)).symm }

instance : Inhabited (α →ₙ+* β) :=
  ⟨0⟩

@[simp]
theorem coe_zero : ⇑(0 : α →ₙ+* β) = 0 :=
  rfl

@[simp]
theorem zero_apply (x : α) : (0 : α →ₙ+* β) x = 0 :=
  rfl

omit rβ

@[simp]
theorem id_apply (x : α) : NonUnitalRingHom.id α x = x :=
  rfl

@[simp]
theorem coe_add_monoid_hom_id : (NonUnitalRingHom.id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_mul_hom_id : (NonUnitalRingHom.id α : α →ₙ* α) = MulHom.id α :=
  rfl

variable {rγ : NonUnitalNonAssocSemiringₓ γ}

include rβ rγ

/-- Composition of non-unital ring homomorphisms is a non-unital ring homomorphism. -/
def comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : α →ₙ+* γ :=
  { g.toMulHom.comp f.toMulHom, g.toAddMonoidHom.comp f.toAddMonoidHom with }

/-- Composition of non-unital ring homomorphisms is associative. -/
theorem comp_assoc {δ} {rδ : NonUnitalNonAssocSemiringₓ δ} (f : α →ₙ+* β) (g : β →ₙ+* γ) (h : γ →ₙ+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (g : β →ₙ+* γ) (f : α →ₙ+* β) : ⇑(g.comp f) = g ∘ f :=
  rfl

@[simp]
theorem comp_apply (g : β →ₙ+* γ) (f : α →ₙ+* β) (x : α) : g.comp f x = g (f x) :=
  rfl

@[simp]
theorem coe_comp_add_monoid_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) : (g.comp f : α →+ γ) = (g : β →+ γ).comp f :=
  rfl

@[simp]
theorem coe_comp_mul_hom (g : β →ₙ+* γ) (f : α →ₙ+* β) : (g.comp f : α →ₙ* γ) = (g : β →ₙ* γ).comp f :=
  rfl

@[simp]
theorem comp_zero (g : β →ₙ+* γ) : g.comp (0 : α →ₙ+* β) = 0 := by
  ext
  simp

@[simp]
theorem zero_comp (f : α →ₙ+* β) : (0 : β →ₙ+* γ).comp f = 0 := by
  ext
  rfl

omit rγ

@[simp]
theorem comp_id (f : α →ₙ+* β) : f.comp (NonUnitalRingHom.id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →ₙ+* β) : (NonUnitalRingHom.id β).comp f = f :=
  ext fun x => rfl

omit rβ

instance : MonoidWithZeroₓ (α →ₙ+* α) where
  one := NonUnitalRingHom.id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc := fun f g h => comp_assoc _ _ _
  zero := 0
  mul_zero := comp_zero
  zero_mul := zero_comp

theorem one_def : (1 : α →ₙ+* α) = NonUnitalRingHom.id α :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : α →ₙ+* α) = id :=
  rfl

theorem mul_def (f g : α →ₙ+* α) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : α →ₙ+* α) : ⇑(f * g) = f ∘ g :=
  rfl

include rβ rγ

theorem cancel_right {g₁ g₂ : β →ₙ+* γ} {f : α →ₙ+* β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩

theorem cancel_left {g : β →ₙ+* γ} {f₁ f₂ : α →ₙ+* β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun x =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    fun h => h ▸ rfl⟩

omit rα rβ rγ

end NonUnitalRingHom

/-- Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.

This extends from both `monoid_hom` and `monoid_with_zero_hom` in order to put the fields in a
sensible order, even though `monoid_with_zero_hom` already extends `monoid_hom`. -/
structure RingHom (α : Type _) (β : Type _) [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] extends α →* β, α →+ β, α →*₀ β

-- mathport name: «expr →+* »
infixr:25 " →+* " => RingHom

/-- Reinterpret a ring homomorphism `f : R →+* S` as a monoid with zero homomorphism `R →*₀ S`.
The `simp`-normal form is `(f : R →*₀ S)`. -/
add_decl_doc RingHom.toMonoidWithZeroHom

/-- Reinterpret a ring homomorphism `f : R →+* S` as a monoid homomorphism `R →* S`.
The `simp`-normal form is `(f : R →* S)`. -/
add_decl_doc RingHom.toMonoidHom

/-- Reinterpret a ring homomorphism `f : R →+* S` as an additive monoid homomorphism `R →+ S`.
The `simp`-normal form is `(f : R →+ S)`. -/
add_decl_doc RingHom.toAddMonoidHom

section RingHomClass

/-- `ring_hom_class F R S` states that `F` is a type of (semi)ring homomorphisms.
You should extend this class when you extend `ring_hom`.

This extends from both `monoid_hom_class` and `monoid_with_zero_hom_class` in
order to put the fields in a sensible order, even though
`monoid_with_zero_hom_class` already extends `monoid_hom_class`. -/
class RingHomClass (F : Type _) (R S : outParam (Type _)) [NonAssocSemiringₓ R] [NonAssocSemiringₓ S] extends
  MonoidHomClass F R S, AddMonoidHomClass F R S, MonoidWithZeroHomClass F R S

variable {F : Type _} [NonAssocSemiringₓ α] [NonAssocSemiringₓ β] [RingHomClass F α β]

/-- Ring homomorphisms preserve `bit1`. -/
@[simp]
theorem map_bit1 (f : F) (a : α) : (f (bit1 a) : β) = bit1 (f a) := by
  simp [bit1]

instance : CoeTₓ F (α →+* β) :=
  ⟨fun f =>
    { toFun := f, map_zero' := map_zero f, map_one' := map_one f, map_mul' := map_mul f, map_add' := map_add f }⟩

instance (priority := 100) RingHomClass.toNonUnitalRingHomClass : NonUnitalRingHomClass F α β :=
  { ‹RingHomClass F α β› with }

end RingHomClass

namespace RingHom

section coe

/-!
Throughout this section, some `semiring` arguments are specified with `{}` instead of `[]`.
See note [implicit instance arguments].
-/


variable {rα : NonAssocSemiringₓ α} {rβ : NonAssocSemiringₓ β}

include rα rβ

instance : RingHomClass (α →+* β) α β where
  coe := RingHom.toFun
  coe_injective' := fun f g h => by
    cases f <;> cases g <;> congr
  map_add := RingHom.map_add'
  map_zero := RingHom.map_zero'
  map_mul := RingHom.map_mul'
  map_one := RingHom.map_one'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly.
-/
instance : CoeFun (α →+* β) fun _ => α → β :=
  ⟨RingHom.toFun⟩

initialize_simps_projections RingHom (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : α →+* β) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : α → β) h₁ h₂ h₃ h₄ : ⇑(⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) = f :=
  rfl

@[simp]
theorem coe_coe {F : Type _} [RingHomClass F α β] (f : F) : ((f : α →+* β) : α → β) = f :=
  rfl

instance hasCoeMonoidHom : Coe (α →+* β) (α →* β) :=
  ⟨RingHom.toMonoidHom⟩

@[simp, norm_cast]
theorem coe_monoid_hom (f : α →+* β) : ⇑(f : α →* β) = f :=
  rfl

@[simp]
theorem to_monoid_hom_eq_coe (f : α →+* β) : f.toMonoidHom = f :=
  rfl

@[simp]
theorem to_monoid_with_zero_hom_eq_coe (f : α →+* β) : (f.toMonoidWithZeroHom : α → β) = f :=
  rfl

@[simp]
theorem coe_monoid_hom_mk (f : α → β) h₁ h₂ h₃ h₄ : ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →* β) = ⟨f, h₁, h₂⟩ :=
  rfl

@[simp, norm_cast]
theorem coe_add_monoid_hom (f : α →+* β) : ⇑(f : α →+ β) = f :=
  rfl

@[simp]
theorem to_add_monoid_hom_eq_coe (f : α →+* β) : f.toAddMonoidHom = f :=
  rfl

@[simp]
theorem coe_add_monoid_hom_mk (f : α → β) h₁ h₂ h₃ h₄ : ((⟨f, h₁, h₂, h₃, h₄⟩ : α →+* β) : α →+ β) = ⟨f, h₃, h₄⟩ :=
  rfl

/-- Copy of a `ring_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
def copy (f : α →+* β) (f' : α → β) (h : f' = f) : α →+* β :=
  { f.toMonoidWithZeroHom.copy f' h, f.toAddMonoidHom.copy f' h with }

end coe

variable [rα : NonAssocSemiringₓ α] [rβ : NonAssocSemiringₓ β]

section

include rα rβ

variable (f : α →+* β) {x y : α} {rα rβ}

theorem congr_fun {f g : α →+* β} (h : f = g) (x : α) : f x = g x :=
  FunLike.congr_fun h x

theorem congr_arg (f : α →+* β) {x y : α} (h : x = y) : f x = f y :=
  FunLike.congr_arg f h

theorem coe_inj ⦃f g : α →+* β⦄ (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h

@[ext]
theorem ext ⦃f g : α →+* β⦄ (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

theorem ext_iff {f g : α →+* β} : f = g ↔ ∀ x, f x = g x :=
  FunLike.ext_iff

@[simp]
theorem mk_coe (f : α →+* β) h₁ h₂ h₃ h₄ : RingHom.mk f h₁ h₂ h₃ h₄ = f :=
  ext fun _ => rfl

theorem coe_add_monoid_hom_injective : Function.Injective (coe : (α →+* β) → α →+ β) := fun f g h =>
  ext fun x => AddMonoidHom.congr_fun h x

theorem coe_monoid_hom_injective : Function.Injective (coe : (α →+* β) → α →* β) := fun f g h =>
  ext fun x => MonoidHom.congr_fun h x

/-- Ring homomorphisms map zero to zero. -/
protected theorem map_zero (f : α →+* β) : f 0 = 0 :=
  map_zero f

/-- Ring homomorphisms map one to one. -/
protected theorem map_one (f : α →+* β) : f 1 = 1 :=
  map_one f

/-- Ring homomorphisms preserve addition. -/
protected theorem map_add (f : α →+* β) (a b : α) : f (a + b) = f a + f b :=
  map_add f a b

/-- Ring homomorphisms preserve multiplication. -/
protected theorem map_mul (f : α →+* β) (a b : α) : f (a * b) = f a * f b :=
  map_mul f a b

/-- Ring homomorphisms preserve `bit0`. -/
protected theorem map_bit0 (f : α →+* β) (a : α) : f (bit0 a) = bit0 (f a) :=
  map_add _ _ _

/-- Ring homomorphisms preserve `bit1`. -/
protected theorem map_bit1 (f : α →+* β) (a : α) : f (bit1 a) = bit1 (f a) := by
  simp [bit1]

/-- `f : R →+* S` has a trivial codomain iff `f 1 = 0`. -/
theorem codomain_trivial_iff_map_one_eq_zero : (0 : β) = 1 ↔ f 1 = 0 := by
  rw [map_one, eq_comm]

/-- `f : R →+* S` has a trivial codomain iff it has a trivial range. -/
theorem codomain_trivial_iff_range_trivial : (0 : β) = 1 ↔ ∀ x, f x = 0 :=
  f.codomain_trivial_iff_map_one_eq_zero.trans
    ⟨fun h x => by
      rw [← mul_oneₓ x, map_mul, h, mul_zero], fun h => h 1⟩

/-- `f : R →+* S` has a trivial codomain iff its range is `{0}`. -/
theorem codomain_trivial_iff_range_eq_singleton_zero : (0 : β) = 1 ↔ Set.Range f = {0} :=
  f.codomain_trivial_iff_range_trivial.trans
    ⟨fun h =>
      Set.ext fun y =>
        ⟨fun ⟨x, hx⟩ => by
          simp [← hx, h x], fun hy =>
          ⟨0, by
            simpa using hy.symm⟩⟩,
      fun h x => Set.mem_singleton_iff.mp (h ▸ Set.mem_range_self x)⟩

/-- `f : R →+* S` doesn't map `1` to `0` if `S` is nontrivial -/
theorem map_one_ne_zero [Nontrivial β] : f 1 ≠ 0 :=
  mt f.codomain_trivial_iff_map_one_eq_zero.mpr zero_ne_one

/-- If there is a homomorphism `f : R →+* S` and `S` is nontrivial, then `R` is nontrivial. -/
theorem domain_nontrivial [Nontrivial β] : Nontrivial α :=
  ⟨⟨1, 0,
      mt
        (fun h =>
          show f 1 = 0 by
            rw [h, map_zero])
        f.map_one_ne_zero⟩⟩

end

theorem is_unit_map [Semiringₓ α] [Semiringₓ β] (f : α →+* β) {a : α} (h : IsUnit a) : IsUnit (f a) :=
  h.map f

/-- The identity ring homomorphism from a semiring to itself. -/
def id (α : Type _) [NonAssocSemiringₓ α] : α →+* α := by
  refine' { toFun := id, .. } <;> intros <;> rfl

include rα

instance : Inhabited (α →+* α) :=
  ⟨id α⟩

@[simp]
theorem id_apply (x : α) : RingHom.id α x = x :=
  rfl

@[simp]
theorem coe_add_monoid_hom_id : (id α : α →+ α) = AddMonoidHom.id α :=
  rfl

@[simp]
theorem coe_monoid_hom_id : (id α : α →* α) = MonoidHom.id α :=
  rfl

variable {rγ : NonAssocSemiringₓ γ}

include rβ rγ

/-- Composition of ring homomorphisms is a ring homomorphism. -/
def comp (hnp : β →+* γ) (hmn : α →+* β) : α →+* γ where
  toFun := hnp ∘ hmn
  map_zero' := by
    simp
  map_one' := by
    simp
  map_add' := fun x y => by
    simp
  map_mul' := fun x y => by
    simp

/-- Composition of semiring homomorphisms is associative. -/
theorem comp_assoc {δ} {rδ : NonAssocSemiringₓ δ} (f : α →+* β) (g : β →+* γ) (h : γ →+* δ) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl

@[simp]
theorem coe_comp (hnp : β →+* γ) (hmn : α →+* β) : (hnp.comp hmn : α → γ) = hnp ∘ hmn :=
  rfl

theorem comp_apply (hnp : β →+* γ) (hmn : α →+* β) (x : α) : (hnp.comp hmn : α → γ) x = hnp (hmn x) :=
  rfl

omit rγ

@[simp]
theorem comp_id (f : α →+* β) : f.comp (id α) = f :=
  ext fun x => rfl

@[simp]
theorem id_comp (f : α →+* β) : (id β).comp f = f :=
  ext fun x => rfl

omit rβ

instance : Monoidₓ (α →+* α) where
  one := id α
  mul := comp
  mul_one := comp_id
  one_mul := id_comp
  mul_assoc := fun f g h => comp_assoc _ _ _

theorem one_def : (1 : α →+* α) = id α :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : α →+* α) = _root_.id :=
  rfl

theorem mul_def (f g : α →+* α) : f * g = f.comp g :=
  rfl

@[simp]
theorem coe_mul (f g : α →+* α) : ⇑(f * g) = f ∘ g :=
  rfl

include rβ rγ

theorem cancel_right {g₁ g₂ : β →+* γ} {f : α →+* β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => RingHom.ext <| hf.forall.2 (ext_iff.1 h), fun h => h ▸ rfl⟩

theorem cancel_left {g : β →+* γ} {f₁ f₂ : α →+* β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    RingHom.ext fun x =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    fun h => h ▸ rfl⟩

omit rα rβ rγ

end RingHom

section Semiringₓ

variable [Semiringₓ α] {a : α}

@[simp]
theorem two_dvd_bit0 : 2 ∣ bit0 a :=
  ⟨a, bit0_eq_two_mul _⟩

theorem RingHom.map_dvd [Semiringₓ β] (f : α →+* β) {a b : α} : a ∣ b → f a ∣ f b :=
  map_dvd f

end Semiringₓ

/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj, ancestor NonUnitalSemiringₓ CommSemigroupₓ]
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiringₓ α, CommSemigroupₓ α

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasScalar ℕ γ] (f : γ → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasScalar ℕ γ] (f : α → γ)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

theorem Dvd.Dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)

end NonUnitalCommSemiring

/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj, ancestor Semiringₓ CommMonoidₓ]
class CommSemiringₓ (α : Type u) extends Semiringₓ α, CommMonoidₓ α

-- see Note [lower instance priority]
instance (priority := 100) CommSemiringₓ.toNonUnitalCommSemiring [CommSemiringₓ α] : NonUnitalCommSemiring α :=
  { CommSemiringₓ.toCommMonoid α, CommSemiringₓ.toSemiring α with }

-- see Note [lower instance priority]
instance (priority := 100) CommSemiringₓ.toCommMonoidWithZero [CommSemiringₓ α] : CommMonoidWithZero α :=
  { CommSemiringₓ.toCommMonoid α, CommSemiringₓ.toSemiring α with }

section CommSemiringₓ

variable [CommSemiringₓ α] [CommSemiringₓ β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasScalar ℕ γ] [Pow γ ℕ] (f : γ → α)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : CommSemiringₓ γ :=
  { hf.Semiring f zero one add mul nsmul npow, hf.CommSemigroup f mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasScalar ℕ γ] [Pow γ ℕ] (f : α → γ)
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : CommSemiringₓ γ :=
  { hf.Semiring f zero one add mul nsmul npow, hf.CommSemigroup f mul with }

theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mulₓ, mul_addₓ, add_assocₓ, mul_comm b]

end CommSemiringₓ

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type _) [Mul α] extends HasInvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by
  simp

theorem neg_mul_eq_neg_mulₓ (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm

theorem neg_mul_comm (a b : α) : -a * b = a * -b := by
  simp

end Mul

section MulOneClassₓ

variable [MulOneClassₓ α] [HasDistribNeg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by
  simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one (a : α) : a * -1 = -a := by
  simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul (a : α) : -1 * a = -a := by
  simp

end MulOneClassₓ

section MulZeroClassₓ

variable [MulZeroClassₓ α] [HasDistribNeg α]

/-- Prefer `neg_zero` if `add_comm_group` is available. -/
@[simp]
theorem neg_zero' : (-0 : α) = 0 := by
  rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero]

end MulZeroClassₓ

section Semigroupₓ

variable [Semigroupₓ α] [HasDistribNeg α] {a b c : α}

theorem dvd_neg_of_dvd (h : a ∣ b) : a ∣ -b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by
    simp [hc]⟩

theorem dvd_of_dvd_neg (h : a ∣ -b) : a ∣ b := by
  let t := dvd_neg_of_dvd h
  rwa [neg_negₓ] at t

/-- An element a of a semigroup with a distributive negation divides the negation of an element b
iff a divides b. -/
@[simp]
theorem dvd_neg (a b : α) : a ∣ -b ↔ a ∣ b :=
  ⟨dvd_of_dvd_neg, dvd_neg_of_dvd⟩

theorem neg_dvd_of_dvd (h : a ∣ b) : -a ∣ b :=
  let ⟨c, hc⟩ := h
  ⟨-c, by
    simp [hc]⟩

theorem dvd_of_neg_dvd (h : -a ∣ b) : a ∣ b := by
  let t := neg_dvd_of_dvd h
  rwa [neg_negₓ] at t

/-- The negation of an element a of a semigroup with a distributive negation divides
another element b iff a divides b. -/
@[simp]
theorem neg_dvd (a b : α) : -a ∣ b ↔ a ∣ b :=
  ⟨dvd_of_neg_dvd, neg_dvd_of_dvd⟩

end Semigroupₓ

section Groupₓ

variable [Groupₓ α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_negₓ, mul_left_invₓ]

end Groupₓ

end HasDistribNeg

/-!
### Rings
-/


/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj, ancestor AddCommGroupₓ NonUnitalNonAssocSemiringₓ]
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroupₓ α, NonUnitalNonAssocSemiringₓ α

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_negₓ
  neg_mul := fun a b =>
    (neg_eq_of_add_eq_zeroₓ <| by
        rw [← right_distrib, add_right_negₓ, zero_mul]).symm
  mul_neg := fun a b =>
    (neg_eq_of_add_eq_zeroₓ <| by
        rw [← left_distrib, add_right_negₓ, mul_zero]).symm

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_addₓ a b (-c)

alias mul_sub_left_distrib ← mul_sub

theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mulₓ] using add_mulₓ a (-b) c

alias mul_sub_right_distrib ← sub_mul

variable {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e := by
      simp [add_commₓ]
    _ ↔ a * e + c - b * e = d :=
      Iff.intro
        (fun h => by
          rw [h]
          simp )
        fun h => by
        rw [← h]
        simp
    _ ↔ (a - b) * e + c = d := by
      simp [sub_mul, sub_add_eq_add_sub]
    

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d := fun h =>
  calc
    (a - b) * e + c = a * e + c - b * e := by
      simp [sub_mul, sub_add_eq_add_sub]
    _ = d := by
      rw [h]
      simp [@add_sub_cancel α]
    

end NonUnitalNonAssocRing

/-- An associative but not-necessarily unital ring. -/
@[protect_proj, ancestor NonUnitalNonAssocRing NonUnitalSemiringₓ]
class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiringₓ α

section NonUnitalRing

variable [NonUnitalRing α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β] [HasScalar ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (gsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β] [HasScalar ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (gsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

end NonUnitalRing

/-- A unital but not-necessarily-associative ring. -/
@[protect_proj, ancestor NonUnitalNonAssocRing NonAssocSemiringₓ]
class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiringₓ α

section NonAssocRing

variable [NonAssocRing α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (gsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.MulOneClass f one mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (gsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.MulOneClass f one mul with }

theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by
  rw [sub_mul, one_mulₓ]

theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by
  rw [mul_sub, mul_oneₓ]

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by
  rw [sub_mul, one_mulₓ]

theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by
  rw [mul_sub, mul_oneₓ]

end NonAssocRing

/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj, ancestor AddCommGroupₓ Monoidₓ Distribₓ]
class Ringₓ (α : Type u) extends AddCommGroupₓ α, Monoidₓ α, Distribₓ α

section Ringₓ

variable [Ringₓ α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring 
-- see Note [lower instance priority]
instance (priority := 100) Ringₓ.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ringₓ α› with
    zero_mul := fun a =>
      add_left_cancelₓ <|
        show 0 * a + 0 * a = 0 * a + 0 by
          rw [← add_mulₓ, zero_addₓ, add_zeroₓ],
    mul_zero := fun a =>
      add_left_cancelₓ <|
        show a * 0 + a * 0 = a * 0 + 0 by
          rw [← mul_addₓ, add_zeroₓ, add_zeroₓ] }

-- A (unital, associative) ring is a not-necessarily-associative ring 
-- see Note [lower instance priority]
instance (priority := 100) Ringₓ.toNonAssocRing : NonAssocRing α :=
  { ‹Ringₓ α› with
    zero_mul := fun a =>
      add_left_cancelₓ <|
        show 0 * a + 0 * a = 0 * a + 0 by
          rw [← add_mulₓ, zero_addₓ, add_zeroₓ],
    mul_zero := fun a =>
      add_left_cancelₓ <|
        show a * 0 + a * 0 = a * 0 + 0 by
          rw [← mul_addₓ, add_zeroₓ, add_zeroₓ] }

/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) Ringₓ.toSemiring : Semiringₓ α :=
  { ‹Ringₓ α›, Ringₓ.toNonUnitalRing with }

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β] [HasScalar ℤ β]
    [Pow β ℕ] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Ringₓ β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β] [HasScalar ℤ β]
    [Pow β ℕ] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x)
    (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : Ringₓ β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

end Ringₓ

namespace Units

variable [Ringₓ α] {a b : α}

/-- Each element of the group of units of a ring has an additive inverse. -/
instance : Neg αˣ :=
  ⟨fun u =>
    ⟨-↑u, -↑u⁻¹, by
      simp , by
      simp ⟩⟩

/-- Representing an element of a ring's unit group as an element of the ring commutes with
    mapping this element to its additive inverse. -/
@[simp, norm_cast]
protected theorem coe_neg (u : αˣ) : (↑(-u) : α) = -u :=
  rfl

@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl

instance : HasDistribNeg αˣ where
  neg := Neg.neg
  neg_neg := fun u => Units.ext <| neg_negₓ _
  neg_mul := fun u₁ u₂ => Units.ext <| neg_mul _ _
  mul_neg := fun u₁ u₂ => Units.ext <| mul_neg _ _

end Units

theorem IsUnit.neg [Ringₓ α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit

theorem IsUnit.neg_iff [Ringₓ α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_negₓ a ▸ h.neg, IsUnit.neg⟩

theorem IsUnit.sub_iff [Ringₓ α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl

namespace RingHom

/-- Ring homomorphisms preserve additive inverse. -/
protected theorem map_neg {α β} [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x : α) : f (-x) = -f x :=
  map_neg f x

/-- Ring homomorphisms preserve subtraction. -/
protected theorem map_sub {α β} [NonAssocRing α] [NonAssocRing β] (f : α →+* β) (x y : α) : f (x - y) = f x - f y :=
  map_sub f x y

/-- Makes a ring homomorphism from a monoid homomorphism of rings which preserves addition. -/
def mk' {γ} [NonAssocSemiringₓ α] [NonAssocRing γ] (f : α →* γ) (map_add : ∀ a b : α, f (a + b) = f a + f b) :
    α →+* γ :=
  { AddMonoidHom.mk' f map_add, f with toFun := f }

end RingHom

/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj, ancestor NonUnitalRing CommSemigroupₓ]
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroupₓ α

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj, ancestor Ringₓ CommSemigroupₓ]
class CommRingₓ (α : Type u) extends Ringₓ α, CommMonoidₓ α

-- see Note [lower instance priority]
instance (priority := 100) CommRingₓ.toCommSemiring [s : CommRingₓ α] : CommSemiringₓ α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }

-- see Note [lower instance priority]
instance (priority := 100) CommRingₓ.toNonUnitalCommRing [s : CommRingₓ α] : NonUnitalCommRing α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  rw [sub_eq_add_neg]
  exact dvd_add h₁ (dvd_neg_of_dvd h₂)

theorem dvd_add_iff_left (h : a ∣ c) : a ∣ b ↔ a ∣ b + c :=
  ⟨fun h₂ => dvd_add h₂ h, fun H => by
    have t := dvd_sub H h <;> rwa [add_sub_cancel] at t⟩

theorem dvd_add_iff_right (h : a ∣ b) : a ∣ c ↔ a ∣ b + c := by
  rw [add_commₓ] <;> exact dvd_add_iff_left h

/-- If an element a divides another element c in a commutative ring, a divides the sum of another
  element b with c iff a divides b. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  (dvd_add_iff_left h).symm

/-- If an element a divides another element b in a commutative ring, a divides the sum of b and
  another element c iff a divides c. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c :=
  (dvd_add_iff_right h).symm

theorem dvd_iff_dvd_of_dvd_sub {a b c : α} (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  constructor
  · intro h'
    convert dvd_sub h' h
    exact Eq.symm (sub_sub_self b c)
    
  · intro h'
    convert dvd_add h h'
    exact eq_add_of_sub_eq rfl
    

end NonUnitalRing

section Ringₓ

variable [Ringₓ α] {a b c : α}

theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 :=
  (dvd_add_iff_right (@two_dvd_bit0 _ _ a)).symm

/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)

/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)

end Ringₓ

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ x n : ℕ, f (n • x) = n • f x) (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

attribute [local simp] add_assocₓ add_commₓ add_left_commₓ mul_comm

/-- Vieta's formula for a quadratic equation, relating the coefficients of the polynomial with
  its roots. This particular version states that if we have a root `x` of a monic quadratic
  polynomial, then there is another root `y` such that `x + y` is negative the `a_1` coefficient
  and `x * y` is the `a_0` coefficient. -/
theorem Vieta_formula_quadratic {b c x : α} (h : x * x - b * x + c = 0) :
    ∃ y : α, y * y - b * y + c = 0 ∧ x + y = b ∧ x * y = c := by
  have : c = -(x * x - b * x) := (neg_eq_of_add_eq_zeroₓ h).symm
  have : c = x * (b - x) := by
    subst this <;> simp [mul_sub, mul_comm]
  refine'
    ⟨b - x, _, by
      simp , by
      rw [this]⟩
  rw [this, sub_add, ← sub_mul, sub_self]

theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) : k ∣ a * x - b * y := by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assocₓ, neg_add_cancel_leftₓ]

end NonUnitalCommRing

section CommRingₓ

variable [CommRingₓ α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] [Pow β ℕ] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : CommRingₓ β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow, hf.CommSemigroup f mul with }

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasScalar ℕ β]
    [HasScalar ℤ β] [Pow β ℕ] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ x n : ℕ, f (n • x) = n • f x)
    (zsmul : ∀ x n : ℤ, f (n • x) = n • f x) (npow : ∀ x n : ℕ, f (x ^ n) = f x ^ n) : CommRingₓ β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow, hf.CommSemigroup f mul with }

end CommRingₓ

theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero
    ((add_right_injₓ a).mp
      (by
        simp [h]))

theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero
    (neg_injective
      ((add_right_injₓ a).mp
        (by
          simpa [sub_eq_add_neg] using h)))

/-- Left `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_left_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : ∀ x : α, k * x = 0 → x = 0) :
    IsLeftRegular k := by
  refine' fun h' : k * x = k * y => sub_eq_zero.mp (h _ _)
  rw [mul_sub, sub_eq_zero, h']

/-- Right `mul` by a `k : α` over `[ring α]` is injective, if `k` is not a zero divisor.
The typeclass that restricts all terms of `α` to have this property is `no_zero_divisors`. -/
theorem is_right_regular_of_non_zero_divisor [NonUnitalNonAssocRing α] (k : α) (h : ∀ x : α, x * k = 0 → x = 0) :
    IsRightRegular k := by
  refine' fun h' : x * k = y * k => sub_eq_zero.mp (h _ _)
  rw [sub_mul, sub_eq_zero, h']

theorem is_regular_of_ne_zero' [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} (hk : k ≠ 0) : IsRegular k :=
  ⟨is_left_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_left hk,
    is_right_regular_of_non_zero_divisor k fun x h =>
      (NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero h).resolve_right hk⟩

theorem is_regular_iff_ne_zero' [Nontrivial α] [NonUnitalNonAssocRing α] [NoZeroDivisors α] {k : α} :
    IsRegular k ↔ k ≠ 0 :=
  ⟨fun h => by
    rintro rfl
    exact not_not.mpr h.left not_is_left_regular_zero, is_regular_of_ne_zero'⟩

/-- A ring with no zero divisors is a cancel_monoid_with_zero.

Note this is not an instance as it forms a typeclass loop. -/
@[reducible]
def NoZeroDivisors.toCancelMonoidWithZero [Ringₓ α] [NoZeroDivisors α] : CancelMonoidWithZero α :=
  { (inferInstance : Semiringₓ α) with
    mul_left_cancel_of_ne_zero := fun a b c ha => @IsRegular.left _ _ _ (is_regular_of_ne_zero' ha) _ _,
    mul_right_cancel_of_ne_zero := fun a b c hb => @IsRegular.right _ _ _ (is_regular_of_ne_zero' hb) _ _ }

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj]
class IsDomain (α : Type u) [Ringₓ α] extends NoZeroDivisors α, Nontrivial α : Prop

section IsDomain

section Ringₓ

variable [Ringₓ α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelMonoidWithZero : CancelMonoidWithZero α :=
  NoZeroDivisors.toCancelMonoidWithZero

/-- Pullback an `is_domain` instance along an injective function. -/
protected theorem Function.Injective.is_domain [Ringₓ β] (f : β →+* α) (hf : Injective f) : IsDomain β :=
  { pullback_nonzero f f.map_zero f.map_one, hf.NoZeroDivisors f f.map_zero f.map_mul with }

end Ringₓ

section CommRingₓ

variable [CommRingₓ α] [IsDomain α]

-- see Note [lower instance priority]
instance (priority := 100) IsDomain.toCancelCommMonoidWithZero : CancelCommMonoidWithZero α :=
  { CommSemiringₓ.toCommMonoidWithZero, IsDomain.toCancelMonoidWithZero with }

/-- Makes a ring homomorphism from an additive group homomorphism from a commutative ring to an integral
domain that commutes with self multiplication, assumes that two is nonzero and one is sent to one.
-/
def AddMonoidHom.mkRingHomOfMulSelfOfTwoNeZero [CommRingₓ β] (f : β →+ α) (h : ∀ x, f (x * x) = f x * f x)
    (h_two : (2 : α) ≠ 0) (h_one : f 1 = 1) : β →+* α :=
  { f with map_one' := h_one,
    map_mul' := by
      intro x y
      have hxy := h (x + y)
      rw [mul_addₓ, add_mulₓ, add_mulₓ, f.map_add, f.map_add, f.map_add, f.map_add, h x, h y, add_mulₓ, mul_addₓ,
        mul_addₓ, ← sub_eq_zero, add_commₓ, ← sub_sub, ← sub_sub, ← sub_sub, mul_comm y x, mul_comm (f y) (f x)] at hxy
      simp only [add_assocₓ, add_sub_assoc, add_sub_cancel'_right] at hxy
      rw [sub_sub, ← two_mul, ← add_sub_assoc, ← two_mul, ← mul_sub, mul_eq_zero, sub_eq_zero, or_iff_not_imp_left] at
        hxy
      exact hxy h_two }

@[simp]
theorem AddMonoidHom.coe_fn_mk_ring_hom_of_mul_self_of_two_ne_zero [CommRingₓ β] (f : β →+ α) h h_two h_one :
    (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β → α) = f :=
  rfl

@[simp]
theorem AddMonoidHom.coe_add_monoid_hom_mk_ring_hom_of_mul_self_of_two_ne_zero [CommRingₓ β] (f : β →+ α)
    h h_two h_one : (f.mkRingHomOfMulSelfOfTwoNeZero h h_two h_one : β →+ α) = f := by
  ext
  simp

end CommRingₓ

end IsDomain

namespace SemiconjBy

@[simp]
theorem add_right [Distribₓ R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by
  simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]
theorem add_left [Distribₓ R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a + b) x y :=
  by
  simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_negₓ x ▸ neg_negₓ y ▸ h.neg_right, SemiconjBy.neg_right⟩

theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by
  simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_negₓ a ▸ h.neg_left, SemiconjBy.neg_left⟩

end

section

variable [MulOneClassₓ R] [HasDistribNeg R] {a x y : R}

@[simp]
theorem neg_one_right (a : R) : SemiconjBy a (-1) (-1) :=
  (one_right a).neg_right

@[simp]
theorem neg_one_left (x : R) : SemiconjBy (-1) x x :=
  (SemiconjBy.one_left x).neg_left

end

section

variable [NonUnitalNonAssocRing R] {a b x y x' y' : R}

@[simp]
theorem sub_right (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') : SemiconjBy a (x - x') (y - y') := by
  simpa only [sub_eq_add_neg] using h.add_right h'.neg_right

@[simp]
theorem sub_left (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a - b) x y := by
  simpa only [sub_eq_add_neg] using ha.add_left hb.neg_left

end

end SemiconjBy

namespace Commute

@[simp]
theorem add_right [Distribₓ R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right

@[simp]
theorem add_left [Distribₓ R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left

theorem bit0_right [Distribₓ R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h

theorem bit0_left [Distribₓ R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h

theorem bit1_right [NonAssocSemiringₓ R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)

theorem bit1_left [NonAssocSemiringₓ R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by
  rw [add_mulₓ, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by
  rw [mul_addₓ, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) :
    a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm, sub_eq_zero, add_eq_zero_iff_eq_neg]

section

variable [Mul R] [HasDistribNeg R] {a b : R}

theorem neg_right : Commute a b → Commute a (-b) :=
  SemiconjBy.neg_right

@[simp]
theorem neg_right_iff : Commute a (-b) ↔ Commute a b :=
  SemiconjBy.neg_right_iff

theorem neg_left : Commute a b → Commute (-a) b :=
  SemiconjBy.neg_left

@[simp]
theorem neg_left_iff : Commute (-a) b ↔ Commute a b :=
  SemiconjBy.neg_left_iff

end

section

variable [MulOneClassₓ R] [HasDistribNeg R] {a : R}

@[simp]
theorem neg_one_right (a : R) : Commute a (-1) :=
  SemiconjBy.neg_one_right a

@[simp]
theorem neg_one_left (a : R) : Commute (-1) a :=
  SemiconjBy.neg_one_left a

end

section

variable [NonUnitalNonAssocRing R] {a b c : R}

@[simp]
theorem sub_right : Commute a b → Commute a c → Commute a (b - c) :=
  SemiconjBy.sub_right

@[simp]
theorem sub_left : Commute a c → Commute b c → Commute (a - b) c :=
  SemiconjBy.sub_left

end

end Commute

/-- Representation of a difference of two squares in a commutative ring as a product. -/
theorem mul_self_sub_mul_self [CommRingₓ R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_oneₓ]

theorem mul_self_eq_mul_self_iff [CommRingₓ R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_oneₓ]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem Units.inv_eq_self_iff [Ringₓ R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [Units.ext_iff]
  push_cast
  exact mul_self_eq_one_iff

