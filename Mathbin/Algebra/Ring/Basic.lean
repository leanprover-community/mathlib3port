/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
import Mathbin.Algebra.Regular.Basic
import Mathbin.Algebra.Hom.Group
import Mathbin.Algebra.Opposites

/-!
# Semirings and rings

This file defines semirings, rings and domains. This is analogous to `algebra.group.defs` and
`algebra.group.basic`, the difference being that the former is about `+` and `*` separately, while
the present file is about their interaction.

## Main definitions

* `distrib`: Typeclass for distributivity of multiplication over addition.
* `has_distrib_neg`: Typeclass for commutativity of negation and multiplication. This is useful when
  dealing with multiplicative submonoids which are closed under negation without being closed under
  addition, for example `units`.
* `(non_unital_)(non_assoc_)(semi)ring`: Typeclasses for possibly non-unital or non-associative
  rings and semirings. Some combinations are not defined yet because they haven't found use.

## Tags

`semiring`, `comm_semiring`, `ring`, `comm_ring`, `domain`, `is_domain`, `nonzero`, `units`
-/


universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {R : Type x}

open Function

/-!
### `distrib` class
-/


#print Distrib /-
/-- A typeclass stating that multiplication is left and right distributive
over addition. -/
@[protect_proj]
class Distrib (R : Type _) extends Mul R, Add R where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c
-/

/-- A typeclass stating that multiplication is left distributive over addition. -/
@[protect_proj]
class LeftDistribClass (R : Type _) [Mul R] [Add R] where
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c

/-- A typeclass stating that multiplication is right distributive over addition. -/
@[protect_proj]
class RightDistribClass (R : Type _) [Mul R] [Add R] where
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

-- see Note [lower instance priority]
instance (priority := 100) Distrib.leftDistribClass (R : Type _) [Distrib R] : LeftDistribClass R :=
  ⟨Distrib.left_distrib⟩

-- see Note [lower instance priority]
instance (priority := 100) Distrib.rightDistribClass (R : Type _) [Distrib R] : RightDistribClass R :=
  ⟨Distrib.right_distrib⟩

theorem left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c : R) : a * (b + c) = a * b + a * c :=
  LeftDistribClass.left_distrib a b c

alias left_distrib ← mul_add

theorem right_distrib [Mul R] [Add R] [RightDistribClass R] (a b c : R) : (a + b) * c = a * c + b * c :=
  RightDistribClass.right_distrib a b c

alias right_distrib ← add_mul

theorem distrib_three_right [Mul R] [Add R] [RightDistribClass R] (a b c d : R) :
    (a + b + c) * d = a * d + b * d + c * d := by simp [right_distrib]

/-- Pullback a `distrib` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.distrib {S} [Mul R] [Add R] [Distrib S] (f : R → S) (hf : Injective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distrib R where
  mul := (· * ·)
  add := (· + ·)
  left_distrib x y z := hf <| by simp only [*, left_distrib]
  right_distrib x y z := hf <| by simp only [*, right_distrib]

/-- Pushforward a `distrib` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.distrib {S} [Distrib R] [Add S] [Mul S] (f : R → S) (hf : Surjective f)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  mul := (· * ·)
  add := (· + ·)
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

/-!
### Semirings
-/


#print NonUnitalNonAssocSemiring /-
/-- A not-necessarily-unital, not-necessarily-associative semiring. -/
@[protect_proj]
class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α
-/

#print NonUnitalSemiring /-
/-- An associative but not-necessarily unital semiring. -/
@[protect_proj]
class NonUnitalSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, SemigroupWithZero α
-/

#print NonAssocSemiring /-
/-- A unital but not-necessarily-associative semiring. -/
@[protect_proj]
class NonAssocSemiring (α : Type u) extends NonUnitalNonAssocSemiring α, MulZeroOneClass α, AddCommMonoidWithOne α
-/

#print Semiring /-
/-- A semiring is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), multiplicative monoid (`monoid`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). The actual definition extends `monoid_with_zero`
instead of `monoid` and `mul_zero_class`. -/
@[protect_proj]
class Semiring (α : Type u) extends NonUnitalSemiring α, NonAssocSemiring α, MonoidWithZero α
-/

section InjectiveSurjectiveMaps

variable [Zero β] [Add β] [Mul β] [HasSmul ℕ β]

/-- Pullback a `non_unital_non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiring α] (f : β → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : β → α) (hf : Injective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiring β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pullback a `non_assoc_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v} [Zero β] [One β]
    [Mul β] [Add β] [HasSmul ℕ β] [HasNatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [HasNatCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocSemiring {α : Type u} [NonUnitalNonAssocSemiring α] (f : α → β)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalNonAssocSemiring β :=
  { hf.MulZeroClass f zero mul, hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalSemiring {α : Type u} [NonUnitalSemiring α] (f : α → β) (hf : Surjective f)
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalSemiring β :=
  { hf.NonUnitalNonAssocSemiring f zero add mul nsmul, hf.SemigroupWithZero f zero mul with }

/-- Pushforward a `non_assoc_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocSemiring {α : Type u} [NonAssocSemiring α] {β : Type v} [Zero β] [One β]
    [Add β] [Mul β] [HasSmul ℕ β] [HasNatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) : NonAssocSemiring β :=
  { hf.AddMonoidWithOne f zero one add nsmul nat_cast, hf.NonUnitalNonAssocSemiring f zero add mul nsmul,
    hf.MulOneClass f one mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semiring {α : Type u} [Semiring α] {β : Type v} [Zero β] [One β] [Add β] [Mul β]
    [Pow β ℕ] [HasSmul ℕ β] [HasNatCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) : Semiring β :=
  { hf.NonAssocSemiring f zero one add mul nsmul nat_cast, hf.MonoidWithZero f zero one mul npow,
    hf.AddCommMonoid f zero add nsmul, hf.Distrib f add mul with }

end InjectiveSurjectiveMaps

section HasOneHasAdd

variable [One α] [Add α]

theorem one_add_one_eq_two : 1 + 1 = (2 : α) :=
  rfl

end HasOneHasAdd

section DistribMulOneClass

variable [Add α] [MulOneClass α]

theorem add_one_mul [RightDistribClass α] (a b : α) : (a + 1) * b = a * b + b := by rw [add_mul, one_mul]

theorem mul_add_one [LeftDistribClass α] (a b : α) : a * (b + 1) = a * b + a := by rw [mul_add, mul_one]

theorem one_add_mul [RightDistribClass α] (a b : α) : (1 + a) * b = b + a * b := by rw [add_mul, one_mul]

theorem mul_one_add [LeftDistribClass α] (a b : α) : a * (1 + b) = a + a * b := by rw [mul_add, mul_one]

theorem two_mul [RightDistribClass α] (n : α) : 2 * n = n + n :=
  Eq.trans (right_distrib 1 1 n) (by simp)

theorem bit0_eq_two_mul [RightDistribClass α] (n : α) : bit0 n = 2 * n :=
  (two_mul _).symm

theorem mul_two [LeftDistribClass α] (n : α) : n * 2 = n + n :=
  (left_distrib n 1 1).trans (by simp)

end DistribMulOneClass

section Semiring

variable [Semiring α]

@[to_additive]
theorem mul_ite {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (a * if P then b else c) = if P then a * b else a * c := by split_ifs <;> rfl

@[to_additive]
theorem ite_mul {α} [Mul α] (P : Prop) [Decidable P] (a b c : α) :
    (if P then a else b) * c = if P then a * c else b * c := by split_ifs <;> rfl

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
theorem mul_boole {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (a * if P then 1 else 0) = if P then a else 0 := by simp

@[simp]
theorem boole_mul {α} [MulZeroOneClass α] (P : Prop) [Decidable P] (a : α) :
    (if P then 1 else 0) * a = if P then a else 0 := by simp

theorem ite_mul_zero_left {α : Type _} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = ite P a 0 * b := by by_cases h:P <;> simp [h]

theorem ite_mul_zero_right {α : Type _} [MulZeroClass α] (P : Prop) [Decidable P] (a b : α) :
    ite P (a * b) 0 = a * ite P b 0 := by by_cases h:P <;> simp [h]

theorem ite_and_mul_zero {α : Type _} [MulZeroClass α] (P Q : Prop) [Decidable P] [Decidable Q] (a b : α) :
    ite (P ∧ Q) (a * b) 0 = ite P a 0 * ite Q b 0 := by
  simp only [← ite_and, ite_mul, mul_ite, mul_zero, zero_mul, and_comm']

end Semiring

namespace AddHom

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulLeft {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨(· * ·) r, mul_add r⟩

/-- Left multiplication by an element of a type with distributive multiplication is an `add_hom`. -/
@[simps (config := { fullyApplied := false })]
def mulRight {R : Type _} [Distrib R] (r : R) : AddHom R R :=
  ⟨fun a => a * r, fun _ _ => add_mul _ _ r⟩

end AddHom

section AddHomClass

variable {F : Type _} [NonAssocSemiring α] [NonAssocSemiring β] [AddHomClass F α β]

/-- Additive homomorphisms preserve `bit0`. -/
@[simp]
theorem map_bit0 (f : F) (a : α) : (f (bit0 a) : β) = bit0 (f a) :=
  map_add _ _ _

end AddHomClass

namespace AddMonoidHom

/-- Left multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulLeft {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun := (· * ·) r
  map_zero' := mul_zero r
  map_add' := mul_add r

@[simp]
theorem coe_mul_left {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulLeft r) = (· * ·) r :=
  rfl

/-- Right multiplication by an element of a (semi)ring is an `add_monoid_hom` -/
def mulRight {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : R →+ R where
  toFun a := a * r
  map_zero' := zero_mul r
  map_add' _ _ := add_mul _ _ r

@[simp]
theorem coe_mul_right {R : Type _} [NonUnitalNonAssocSemiring R] (r : R) : ⇑(mulRight r) = (· * r) :=
  rfl

theorem mul_right_apply {R : Type _} [NonUnitalNonAssocSemiring R] (a r : R) : mulRight r a = a * r :=
  rfl

end AddMonoidHom

/-- A non-unital commutative semiring is a `non_unital_semiring` with commutative multiplication.
In other words, it is a type with the following structures: additive commutative monoid
(`add_comm_monoid`), commutative semigroup (`comm_semigroup`), distributive laws (`distrib`), and
multiplication by zero law (`mul_zero_class`). -/
@[protect_proj]
class NonUnitalCommSemiring (α : Type u) extends NonUnitalSemiring α, CommSemigroup α

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

/-- Pullback a `non_unital_semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : γ → α)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommSemiring [Zero γ] [Add γ] [Mul γ] [HasSmul ℕ γ] (f : α → γ)
    (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) : NonUnitalCommSemiring γ :=
  { hf.NonUnitalSemiring f zero add mul nsmul, hf.CommSemigroup f mul with }

end NonUnitalCommSemiring

#print CommSemiring /-
/-- A commutative semiring is a `semiring` with commutative multiplication. In other words, it is a
type with the following structures: additive commutative monoid (`add_comm_monoid`), multiplicative
commutative monoid (`comm_monoid`), distributive laws (`distrib`), and multiplication by zero law
(`mul_zero_class`). -/
@[protect_proj]
class CommSemiring (α : Type u) extends Semiring α, CommMonoid α
-/

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toNonUnitalCommSemiring [CommSemiring α] : NonUnitalCommSemiring α :=
  { CommSemiring.toCommMonoid α, CommSemiring.toSemiring α with }

-- see Note [lower instance priority]
instance (priority := 100) CommSemiring.toCommMonoidWithZero [CommSemiring α] : CommMonoidWithZero α :=
  { CommSemiring.toCommMonoid α, CommSemiring.toSemiring α with }

section CommSemiring

variable [CommSemiring α] [CommSemiring β] {a b c : α}

/-- Pullback a `semiring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [HasNatCast γ] [Pow γ ℕ]
    (f : γ → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiring γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }

/-- Pushforward a `semiring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commSemiring [Zero γ] [One γ] [Add γ] [Mul γ] [HasSmul ℕ γ] [HasNatCast γ] [Pow γ ℕ]
    (f : α → γ) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (nat_cast : ∀ n : ℕ, f n = n) : CommSemiring γ :=
  { hf.Semiring f zero one add mul nsmul npow nat_cast, hf.CommSemigroup f mul with }

theorem add_mul_self_eq (a b : α) : (a + b) * (a + b) = a * a + 2 * a * b + b * b := by
  simp only [two_mul, add_mul, mul_add, add_assoc, mul_comm b]

end CommSemiring

section HasDistribNeg

/-- Typeclass for a negation operator that distributes across multiplication.

This is useful for dealing with submonoids of a ring that contain `-1` without having to duplicate
lemmas. -/
class HasDistribNeg (α : Type _) [Mul α] extends HasInvolutiveNeg α where
  neg_mul : ∀ x y : α, -x * y = -(x * y)
  mul_neg : ∀ x y : α, x * -y = -(x * y)

section Mul

variable [Mul α] [HasDistribNeg α]

/- warning: neg_mul -> neg_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Mul.{u} α] [_inst_2 : HasDistribNeg.{u} α _inst_1] (a : α) (b : α), Eq.{succ u} α (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) a) b) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) a b))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.655 : Ring.{u_1} R] (a : R) (b : R), Eq.{succ u_1} R (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.655))))) (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.655) a) b) (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.655) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.655))))) a b))
Case conversion may be inaccurate. Consider using '#align neg_mul neg_mulₓ'. -/
@[simp]
theorem neg_mul (a b : α) : -a * b = -(a * b) :=
  HasDistribNeg.neg_mul _ _

/- warning: mul_neg -> mul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Mul.{u} α] [_inst_2 : HasDistribNeg.{u} α _inst_1] (a : α) (b : α), Eq.{succ u} α (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) a (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) b)) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) a b))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.713 : Ring.{u_1} R] (a : R) (b : R), Eq.{succ u_1} R (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.713))))) a (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.713) b)) (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.713) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.713))))) a b))
Case conversion may be inaccurate. Consider using '#align mul_neg mul_negₓ'. -/
@[simp]
theorem mul_neg (a b : α) : a * -b = -(a * b) :=
  HasDistribNeg.mul_neg _ _

theorem neg_mul_neg (a b : α) : -a * -b = a * b := by simp

/- warning: neg_mul_eq_neg_mul -> neg_mul_eq_neg_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u}} [_inst_1 : Mul.{u} α] [_inst_2 : HasDistribNeg.{u} α _inst_1] (a : α) (b : α), Eq.{succ u} α (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) a b)) (HMul.hMul.{u u u} α α α (instHMul.{u} α _inst_1) (Neg.neg.{u} α (HasInvolutiveNeg.toHasNeg.{u} α (HasDistribNeg.toHasInvolutiveNeg.{u} α _inst_1 _inst_2)) a) b)
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.767 : Ring.{u_1} R] (a : R) (b : R), Eq.{succ u_1} R (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.767) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.767))))) a b)) (HMul.hMul.{u_1 u_1 u_1} R R R (instHMul.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R (Ring.toSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.767))))) (Neg.neg.{u_1} R (Ring.toNeg.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.767) a) b)
Case conversion may be inaccurate. Consider using '#align neg_mul_eq_neg_mul neg_mul_eq_neg_mulₓ'. -/
theorem neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b :=
  (neg_mul _ _).symm

theorem neg_mul_eq_mul_neg (a b : α) : -(a * b) = a * -b :=
  (mul_neg _ _).symm

theorem neg_mul_comm (a b : α) : -a * b = a * -b := by simp

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
@[reducible]
protected def Function.Injective.hasDistribNeg [Neg β] [Mul β] (f : β → α) (hf : Injective f) (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with neg_mul := fun x y => hf <| by erw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by erw [neg, mul, neg, mul_neg, mul] }

-- See note [reducible non-instances]
/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
@[reducible]
protected def Function.Surjective.hasDistribNeg [Neg β] [Mul β] (f : α → β) (hf : Surjective f)
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg β :=
  { hf.HasInvolutiveNeg _ neg, ‹Mul β› with
    neg_mul :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, neg_mul, neg, mul]
        rfl,
    mul_neg :=
      hf.Forall₂.2 fun x y => by
        erw [← neg, ← mul, mul_neg, neg, mul]
        rfl }

namespace AddOpposite

instance : HasDistribNeg αᵃᵒᵖ :=
  unop_injective.HasDistribNeg _ unop_neg unop_mul

end AddOpposite

open MulOpposite

instance : HasDistribNeg αᵐᵒᵖ :=
  { MulOpposite.hasInvolutiveNeg _ with neg_mul := fun _ _ => unop_injective <| mul_neg _ _,
    mul_neg := fun _ _ => unop_injective <| neg_mul _ _ }

end Mul

section MulOneClass

variable [MulOneClass α] [HasDistribNeg α]

theorem neg_eq_neg_one_mul (a : α) : -a = -1 * a := by simp

/-- An element of a ring multiplied by the additive inverse of one is the element's additive
  inverse. -/
theorem mul_neg_one (a : α) : a * -1 = -a := by simp

/-- The additive inverse of one multiplied by an element of a ring is the element's additive
  inverse. -/
theorem neg_one_mul (a : α) : -1 * a = -a := by simp

end MulOneClass

section MulZeroClass

variable [MulZeroClass α] [HasDistribNeg α]

instance (priority := 100) MulZeroClass.negZeroClass : NegZeroClass α :=
  { MulZeroClass.toHasZero α, HasDistribNeg.toHasInvolutiveNeg α with
    neg_zero := by rw [← zero_mul (0 : α), ← neg_mul, mul_zero, mul_zero] }

end MulZeroClass

section Group

variable [Group α] [HasDistribNeg α]

@[simp]
theorem inv_neg' (a : α) : (-a)⁻¹ = -a⁻¹ := by
  rw [eq_comm, eq_inv_iff_mul_eq_one, neg_mul, mul_neg, neg_neg, mul_left_inv]

end Group

end HasDistribNeg

/-!
### Rings
-/


/-- A not-necessarily-unital, not-necessarily-associative ring. -/
@[protect_proj]
class NonUnitalNonAssocRing (α : Type u) extends AddCommGroup α, NonUnitalNonAssocSemiring α

section NonUnitalNonAssocRing

variable [NonUnitalNonAssocRing α]

/-- Pullback a `non_unital_non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

/-- Pushforward a `non_unital_non_assoc_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalNonAssocRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) :
    NonUnitalNonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul with }

instance (priority := 100) NonUnitalNonAssocRing.toHasDistribNeg : HasDistribNeg α where
  neg := Neg.neg
  neg_neg := neg_neg
  neg_mul a b := eq_neg_of_add_eq_zero_left <| by rw [← right_distrib, add_left_neg, zero_mul]
  mul_neg a b := eq_neg_of_add_eq_zero_left <| by rw [← left_distrib, add_left_neg, mul_zero]

theorem mul_sub_left_distrib (a b c : α) : a * (b - c) = a * b - a * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_mul_neg] using mul_add a b (-c)

alias mul_sub_left_distrib ← mul_sub

#print mul_sub_right_distrib /-
theorem mul_sub_right_distrib (a b c : α) : (a - b) * c = a * c - b * c := by
  simpa only [sub_eq_add_neg, neg_mul_eq_neg_mul] using add_mul a (-b) c
-/

alias mul_sub_right_distrib ← sub_mul

variable {a b c d e : α}

/-- An iff statement following from right distributivity in rings and the definition
  of subtraction. -/
theorem mul_add_eq_mul_add_iff_sub_mul_add_eq : a * e + c = b * e + d ↔ (a - b) * e + c = d :=
  calc
    a * e + c = b * e + d ↔ a * e + c = d + b * e := by simp [add_comm]
    _ ↔ a * e + c - b * e = d :=
      Iff.intro
        (fun h => by
          rw [h]
          simp)
        fun h => by
        rw [← h]
        simp
    _ ↔ (a - b) * e + c = d := by simp [sub_mul, sub_add_eq_add_sub]
    

/-- A simplification of one side of an equation exploiting right distributivity in rings
  and the definition of subtraction. -/
theorem sub_mul_add_eq_of_mul_add_eq_mul_add : a * e + c = b * e + d → (a - b) * e + c = d := fun h =>
  calc
    (a - b) * e + c = a * e + c - b * e := by simp [sub_mul, sub_add_eq_add_sub]
    _ = d := by
      rw [h]
      simp [@add_sub_cancel α]
    

end NonUnitalNonAssocRing

/-- An associative but not-necessarily unital ring. -/
@[protect_proj]
class NonUnitalRing (α : Type _) extends NonUnitalNonAssocRing α, NonUnitalSemiring α

section NonUnitalRing

variable [NonUnitalRing α]

/-- Pullback a `non_unital_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul, hf.Distrib f add mul,
    hf.Semigroup f mul with }

end NonUnitalRing

/-- A unital but not-necessarily-associative ring. -/
@[protect_proj]
class NonAssocRing (α : Type _) extends NonUnitalNonAssocRing α, NonAssocSemiring α, AddGroupWithOne α

section NonAssocRing

variable [NonAssocRing α]

/-- Pullback a `non_assoc_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.MulZeroClass f zero mul,
    hf.Distrib f add mul, hf.MulOneClass f one mul with }

/-- Pushforward a `non_unital_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonAssocRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β]
    [HasSmul ℤ β] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (gsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) :
    NonAssocRing β :=
  { hf.AddCommGroup f zero add neg sub nsmul gsmul, hf.MulZeroClass f zero mul,
    hf.AddGroupWithOne f zero one add neg sub nsmul gsmul nat_cast int_cast, hf.Distrib f add mul,
    hf.MulOneClass f one mul with }

theorem sub_one_mul (a b : α) : (a - 1) * b = a * b - b := by rw [sub_mul, one_mul]

theorem mul_sub_one (a b : α) : a * (b - 1) = a * b - a := by rw [mul_sub, mul_one]

theorem one_sub_mul (a b : α) : (1 - a) * b = b - a * b := by rw [sub_mul, one_mul]

theorem mul_one_sub (a b : α) : a * (1 - b) = a - a * b := by rw [mul_sub, mul_one]

end NonAssocRing

#print Ring /-
/-- A ring is a type with the following structures: additive commutative group (`add_comm_group`),
multiplicative monoid (`monoid`), and distributive laws (`distrib`).  Equivalently, a ring is a
`semiring` with a negation operation making it an additive group.  -/
@[protect_proj]
class Ring (α : Type u) extends AddCommGroupWithOne α, Monoid α, Distrib α
-/

section Ring

variable [Ring α] {a b c d e : α}

-- A (unital, associative) ring is a not-necessarily-unital ring 
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonUnitalRing : NonUnitalRing α :=
  { ‹Ring α› with
    zero_mul := fun a => add_left_cancel <| show 0 * a + 0 * a = 0 * a + 0 by rw [← add_mul, zero_add, add_zero],
    mul_zero := fun a => add_left_cancel <| show a * 0 + a * 0 = a * 0 + 0 by rw [← mul_add, add_zero, add_zero] }

-- A (unital, associative) ring is a not-necessarily-associative ring 
-- see Note [lower instance priority]
instance (priority := 100) Ring.toNonAssocRing : NonAssocRing α :=
  { ‹Ring α› with
    zero_mul := fun a => add_left_cancel <| show 0 * a + 0 * a = 0 * a + 0 by rw [← add_mul, zero_add, add_zero],
    mul_zero := fun a => add_left_cancel <| show a * 0 + a * 0 = a * 0 + 0 by rw [← mul_add, add_zero, add_zero] }

#print Ring.toSemiring /-
/- The instance from `ring` to `semiring` happens often in linear algebra, for which all the basic
definitions are given in terms of semirings, but many applications use rings or fields. We increase
a little bit its priority above 100 to try it quickly, but remaining below the default 1000 so that
more specific instances are tried first. -/
instance (priority := 200) Ring.toSemiring : Semiring α :=
  { ‹Ring α›, Ring.toNonUnitalRing with }
-/

/-- Pullback a `ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ring β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

/-- Pushforward a `ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.ring [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : Ring β :=
  { hf.AddGroupWithOne f zero one add neg sub nsmul zsmul nat_cast int_cast,
    hf.AddCommGroup f zero add neg sub nsmul zsmul, hf.Monoid f one mul npow, hf.Distrib f add mul with }

end Ring

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

@[simp, norm_cast]
protected theorem coe_neg_one : ((-1 : αˣ) : α) = -1 :=
  rfl

instance : HasDistribNeg αˣ :=
  Units.ext.HasDistribNeg _ Units.coe_neg Units.coe_mul

@[field_simps]
theorem neg_divp (a : α) (u : αˣ) : -(a /ₚ u) = -a /ₚ u := by simp only [divp, neg_mul]

end HasDistribNeg

section Ring

variable [Ring α] {a b : α}

@[field_simps]
theorem divp_add_divp_same (a b : α) (u : αˣ) : a /ₚ u + b /ₚ u = (a + b) /ₚ u := by simp only [divp, add_mul]

@[field_simps]
theorem divp_sub_divp_same (a b : α) (u : αˣ) : a /ₚ u - b /ₚ u = (a - b) /ₚ u := by
  rw [sub_eq_add_neg, sub_eq_add_neg, neg_divp, divp_add_divp_same]

@[field_simps]
theorem add_divp (a b : α) (u : αˣ) : a + b /ₚ u = (a * u + b) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

@[field_simps]
theorem sub_divp (a b : α) (u : αˣ) : a - b /ₚ u = (a * u - b) /ₚ u := by
  simp only [divp, sub_mul, Units.mul_inv_cancel_right]

@[field_simps]
theorem divp_add (a b : α) (u : αˣ) : a /ₚ u + b = (a + b * u) /ₚ u := by
  simp only [divp, add_mul, Units.mul_inv_cancel_right]

@[field_simps]
theorem divp_sub (a b : α) (u : αˣ) : a /ₚ u - b = (a - b * u) /ₚ u := by
  simp only [divp, sub_mul, sub_right_inj]
  assoc_rw [Units.mul_inv, mul_one]

end Ring

end Units

theorem IsUnit.neg [Monoid α] [HasDistribNeg α] {a : α} : IsUnit a → IsUnit (-a)
  | ⟨x, hx⟩ => hx ▸ (-x).IsUnit

@[simp]
theorem IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : IsUnit (-a) ↔ IsUnit a :=
  ⟨fun h => neg_neg a ▸ h.neg, IsUnit.neg⟩

theorem IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsUnit (y - x) :=
  (IsUnit.neg_iff _).symm.trans <| neg_sub x y ▸ Iff.rfl

namespace RingHom

end RingHom

/-- A non-unital commutative ring is a `non_unital_ring` with commutative multiplication. -/
@[protect_proj]
class NonUnitalCommRing (α : Type u) extends NonUnitalRing α, CommSemigroup α

-- see Note [lower instance priority]
instance (priority := 100) NonUnitalCommRing.toNonUnitalCommSemiring [s : NonUnitalCommRing α] :
    NonUnitalCommSemiring α :=
  { s with }

#print CommRing /-
/-- A commutative ring is a `ring` with commutative multiplication. -/
@[protect_proj]
class CommRing (α : Type u) extends Ring α, CommMonoid α
-/

#print CommRing.toCommSemiring /-
-- see Note [lower instance priority]
instance (priority := 100) CommRing.toCommSemiring [s : CommRing α] : CommSemiring α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }
-/

-- see Note [lower instance priority]
instance (priority := 100) CommRing.toNonUnitalCommRing [s : CommRing α] : NonUnitalCommRing α :=
  { s with mul_zero := mul_zero, zero_mul := zero_mul }

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : β → α) (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

/-- Pushforward a `non_unital_comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.nonUnitalCommRing [Zero β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x) (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) : NonUnitalCommRing β :=
  { hf.NonUnitalRing f zero add mul neg sub nsmul zsmul, hf.CommSemigroup f mul with }

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

end NonUnitalCommRing

section CommRing

variable [CommRing α] {a b c : α}

/-- Pullback a `comm_ring` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : β → α) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }

/-- Pushforward a `comm_ring` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commRing [Zero β] [One β] [Add β] [Mul β] [Neg β] [Sub β] [HasSmul ℕ β] [HasSmul ℤ β]
    [Pow β ℕ] [HasNatCast β] [HasIntCast β] (f : α → β) (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (x) (n : ℕ), f (n • x) = n • f x)
    (zsmul : ∀ (x) (n : ℤ), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (nat_cast : ∀ n : ℕ, f n = n) (int_cast : ∀ n : ℤ, f n = n) : CommRing β :=
  { hf.Ring f zero one add mul neg sub nsmul zsmul npow nat_cast int_cast, hf.CommSemigroup f mul with }

end CommRing

theorem succ_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a + 1 ≠ a := fun h =>
  one_ne_zero ((add_right_inj a).mp (by simp [h]))

theorem pred_ne_self [NonAssocRing α] [Nontrivial α] (a : α) : a - 1 ≠ a := fun h =>
  one_ne_zero (neg_injective ((add_right_inj a).mp (by simpa [sub_eq_add_neg] using h)))

/-- A domain is a nontrivial ring with no zero divisors, i.e. satisfying
  the condition `a * b = 0 ↔ a = 0 ∨ b = 0`.

  This is implemented as a mixin for `ring α`.
  To obtain an integral domain use `[comm_ring α] [is_domain α]`. -/
@[protect_proj]
class IsDomain (α : Type u) [Ring α] extends NoZeroDivisors α, Nontrivial α : Prop

namespace SemiconjBy

@[simp]
theorem add_right [Distrib R] {a x y x' y' : R} (h : SemiconjBy a x y) (h' : SemiconjBy a x' y') :
    SemiconjBy a (x + x') (y + y') := by simp only [SemiconjBy, left_distrib, right_distrib, h.eq, h'.eq]

@[simp]
theorem add_left [Distrib R] {a b x y : R} (ha : SemiconjBy a x y) (hb : SemiconjBy b x y) : SemiconjBy (a + b) x y :=
  by simp only [SemiconjBy, left_distrib, right_distrib, ha.eq, hb.eq]

section

variable [Mul R] [HasDistribNeg R] {a x y : R}

theorem neg_right (h : SemiconjBy a x y) : SemiconjBy a (-x) (-y) := by simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
theorem neg_right_iff : SemiconjBy a (-x) (-y) ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg x ▸ neg_neg y ▸ h.neg_right, SemiconjBy.neg_right⟩

theorem neg_left (h : SemiconjBy a x y) : SemiconjBy (-a) x y := by simp only [SemiconjBy, h.eq, neg_mul, mul_neg]

@[simp]
theorem neg_left_iff : SemiconjBy (-a) x y ↔ SemiconjBy a x y :=
  ⟨fun h => neg_neg a ▸ h.neg_left, SemiconjBy.neg_left⟩

end

section

variable [MulOneClass R] [HasDistribNeg R] {a x y : R}

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

/- warning: commute.add_right -> Commute.add_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a b) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a (HAdd.hAdd.{x x x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) b c))
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.236 : Semiring.{u_1} R] {a : R} {b : R} {c : R}, (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a b) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))) a (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.236))))) b c))
Case conversion may be inaccurate. Consider using '#align commute.add_right Commute.add_rightₓ'. -/
@[simp]
theorem add_right [Distrib R] {a b c : R} : Commute a b → Commute a c → Commute a (b + c) :=
  SemiconjBy.add_right

/- warning: commute.add_left -> Commute.add_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{x}} [_inst_1 : Distrib.{x} R] {a : R} {b : R} {c : R}, (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) a c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) b c) -> (Commute.{x} R (Distrib.toHasMul.{x} R _inst_1) (HAdd.hAdd.{x x x} R R R (instHAdd.{x} R (Distrib.toHasAdd.{x} R _inst_1)) a b) c)
but is expected to have type
  forall {R : Type.{u_1}} [inst._@.Mathlib.Algebra.Ring.Basic._hyg.271 : Semiring.{u_1} R] {a : R} {b : R} {c : R}, (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) a c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) b c) -> (Commute.{u_1} R (NonUnitalNonAssocSemiring.toMul.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))) (HAdd.hAdd.{u_1 u_1 u_1} R R R (instHAdd.{u_1} R (Distrib.toAdd.{u_1} R (NonUnitalNonAssocSemiring.toDistrib.{u_1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u_1} R (Semiring.toNonAssocSemiring.{u_1} R inst._@.Mathlib.Algebra.Ring.Basic._hyg.271))))) a b) c)
Case conversion may be inaccurate. Consider using '#align commute.add_left Commute.add_leftₓ'. -/
@[simp]
theorem add_left [Distrib R] {a b c : R} : Commute a c → Commute b c → Commute (a + b) c :=
  SemiconjBy.add_left

theorem bit0_right [Distrib R] {x y : R} (h : Commute x y) : Commute x (bit0 y) :=
  h.add_right h

theorem bit0_left [Distrib R] {x y : R} (h : Commute x y) : Commute (bit0 x) y :=
  h.add_left h

theorem bit1_right [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute x (bit1 y) :=
  h.bit0_right.add_right (Commute.one_right x)

theorem bit1_left [NonAssocSemiring R] {x y : R} (h : Commute x y) : Commute (bit1 x) y :=
  h.bit0_left.add_left (Commute.one_left y)

/-- Representation of a difference of two squares of commuting elements as a product. -/
theorem mul_self_sub_mul_self_eq [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a + b) * (a - b) := by rw [add_mul, mul_sub, mul_sub, h.eq, sub_add_sub_cancel]

theorem mul_self_sub_mul_self_eq' [NonUnitalNonAssocRing R] {a b : R} (h : Commute a b) :
    a * a - b * b = (a - b) * (a + b) := by rw [mul_add, sub_mul, sub_mul, h.eq, sub_add_sub_cancel]

theorem mul_self_eq_mul_self_iff [NonUnitalNonAssocRing R] [NoZeroDivisors R] {a b : R} (h : Commute a b) :
    a * a = b * b ↔ a = b ∨ a = -b := by
  rw [← sub_eq_zero, h.mul_self_sub_mul_self_eq, mul_eq_zero, or_comm', sub_eq_zero, add_eq_zero_iff_eq_neg]

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

variable [MulOneClass R] [HasDistribNeg R] {a : R}

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
theorem mul_self_sub_mul_self [CommRing R] (a b : R) : a * a - b * b = (a + b) * (a - b) :=
  (Commute.all a b).mul_self_sub_mul_self_eq

theorem mul_self_sub_one [NonAssocRing R] (a : R) : a * a - 1 = (a + 1) * (a - 1) := by
  rw [← (Commute.one_right a).mul_self_sub_mul_self_eq, mul_one]

theorem mul_self_eq_mul_self_iff [CommRing R] [NoZeroDivisors R] {a b : R} : a * a = b * b ↔ a = b ∨ a = -b :=
  (Commute.all a b).mul_self_eq_mul_self_iff

theorem mul_self_eq_one_iff [NonAssocRing R] [NoZeroDivisors R] {a : R} : a * a = 1 ↔ a = 1 ∨ a = -1 := by
  rw [← (Commute.one_right a).mul_self_eq_mul_self_iff, mul_one]

namespace Units

@[field_simps]
theorem divp_add_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) : a /ₚ u₁ + b /ₚ u₂ = (a * u₂ + u₁ * b) /ₚ (u₁ * u₂) := by
  simp only [divp, add_mul, mul_inv_rev, coe_mul]
  rw [mul_comm (↑u₁ * b), mul_comm b]
  assoc_rw [mul_inv, mul_inv, mul_one, mul_one]

@[field_simps]
theorem divp_sub_divp [CommRing α] (a b : α) (u₁ u₂ : αˣ) : a /ₚ u₁ - b /ₚ u₂ = (a * u₂ - u₁ * b) /ₚ (u₁ * u₂) := by
  simp_rw [sub_eq_add_neg, neg_divp, divp_add_divp, mul_neg]

/-- In the unit group of an integral domain, a unit is its own inverse iff the unit is one or
  one's additive inverse. -/
theorem inv_eq_self_iff [Ring R] [NoZeroDivisors R] (u : Rˣ) : u⁻¹ = u ↔ u = 1 ∨ u = -1 := by
  rw [inv_eq_iff_mul_eq_one]
  simp only [ext_iff]
  push_cast
  exact mul_self_eq_one_iff

end Units

/-! ### Order dual -/


instance [h : Distrib α] : Distrib αᵒᵈ :=
  h

instance [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass αᵒᵈ :=
  h

instance [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass αᵒᵈ :=
  h

instance [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring αᵒᵈ :=
  h

instance [h : NonUnitalSemiring α] : NonUnitalSemiring αᵒᵈ :=
  h

instance [h : NonAssocSemiring α] : NonAssocSemiring αᵒᵈ :=
  h

instance [h : Semiring α] : Semiring αᵒᵈ :=
  h

instance [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring αᵒᵈ :=
  h

instance [h : CommSemiring α] : CommSemiring αᵒᵈ :=
  h

instance [Mul α] [h : HasDistribNeg α] : HasDistribNeg αᵒᵈ :=
  h

instance [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing αᵒᵈ :=
  h

instance [h : NonUnitalRing α] : NonUnitalRing αᵒᵈ :=
  h

instance [h : NonAssocRing α] : NonAssocRing αᵒᵈ :=
  h

instance [h : Ring α] : Ring αᵒᵈ :=
  h

instance [h : NonUnitalCommRing α] : NonUnitalCommRing αᵒᵈ :=
  h

instance [h : CommRing α] : CommRing αᵒᵈ :=
  h

instance [Ring α] [h : IsDomain α] : IsDomain αᵒᵈ :=
  h

/-! ### Lexicographical order -/


instance [h : Distrib α] : Distrib (Lex α) :=
  h

instance [Mul α] [Add α] [h : LeftDistribClass α] : LeftDistribClass (Lex α) :=
  h

instance [Mul α] [Add α] [h : RightDistribClass α] : RightDistribClass (Lex α) :=
  h

instance [h : NonUnitalNonAssocSemiring α] : NonUnitalNonAssocSemiring (Lex α) :=
  h

instance [h : NonUnitalSemiring α] : NonUnitalSemiring (Lex α) :=
  h

instance [h : NonAssocSemiring α] : NonAssocSemiring (Lex α) :=
  h

instance [h : Semiring α] : Semiring (Lex α) :=
  h

instance [h : NonUnitalCommSemiring α] : NonUnitalCommSemiring (Lex α) :=
  h

instance [h : CommSemiring α] : CommSemiring (Lex α) :=
  h

instance [Mul α] [h : HasDistribNeg α] : HasDistribNeg (Lex α) :=
  h

instance [h : NonUnitalNonAssocRing α] : NonUnitalNonAssocRing (Lex α) :=
  h

instance [h : NonUnitalRing α] : NonUnitalRing (Lex α) :=
  h

instance [h : NonAssocRing α] : NonAssocRing (Lex α) :=
  h

instance [h : Ring α] : Ring (Lex α) :=
  h

instance [h : NonUnitalCommRing α] : NonUnitalCommRing (Lex α) :=
  h

instance [h : CommRing α] : CommRing (Lex α) :=
  h

instance [Ring α] [h : IsDomain α] : IsDomain (Lex α) :=
  h

