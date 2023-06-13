/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Simon Hudon, Mario Carneiro

! This file was ported from Lean 3 source module algebra.group.basic
! leanprover-community/mathlib commit a07d750983b94c530ab69a726862c2ab6802b38c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Group.Defs

/-!
# Basic lemmas about semigroups, monoids, and groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file lists various basic lemmas about semigroups, monoids, and groups. Most proofs are
one-liners from the corresponding axioms. For the definitions of semigroups, monoids and groups, see
`algebra/group/defs.lean`.
-/


open Function

universe u

variable {α β G : Type _}

section Associative

variable (f : α → α → α) [IsAssociative α f] (x y : α)

/-- Composing two associative operations of `f : α → α → α` on the left
is equal to an associative operation on the left.
-/
theorem comp_assoc_left : f x ∘ f y = f (f x y) := by ext z;
  rw [Function.comp_apply, @IsAssociative.assoc _ f]
#align comp_assoc_left comp_assoc_left

/-- Composing two associative operations of `f : α → α → α` on the right
is equal to an associative operation on the right.
-/
theorem comp_assoc_right : ((fun z => f z x) ∘ fun z => f z y) = fun z => f z (f y x) := by ext z;
  rw [Function.comp_apply, @IsAssociative.assoc _ f]
#align comp_assoc_right comp_assoc_right

end Associative

section Semigroup

#print comp_mul_left /-
/-- Composing two multiplications on the left by `y` then `x`
is equal to a multiplication on the left by `x * y`.
-/
@[simp,
  to_additive
      "Composing two additions on the left by `y` then `x`\nis equal to a addition on the left by `x + y`."]
theorem comp_mul_left [Semigroup α] (x y : α) : (· * ·) x ∘ (· * ·) y = (· * ·) (x * y) :=
  comp_assoc_left _ _ _
#align comp_mul_left comp_mul_left
#align comp_add_left comp_add_left
-/

#print comp_mul_right /-
/-- Composing two multiplications on the right by `y` and `x`
is equal to a multiplication on the right by `y * x`.
-/
@[simp,
  to_additive
      "Composing two additions on the right by `y` and `x`\nis equal to a addition on the right by `y + x`."]
theorem comp_mul_right [Semigroup α] (x y : α) : (· * x) ∘ (· * y) = (· * (y * x)) :=
  comp_assoc_right _ _ _
#align comp_mul_right comp_mul_right
#align comp_add_right comp_add_right
-/

end Semigroup

section MulOneClass

variable {M : Type u} [MulOneClass M]

#print ite_mul_one /-
@[to_additive]
theorem ite_mul_one {P : Prop} [Decidable P] {a b : M} : ite P (a * b) 1 = ite P a 1 * ite P b 1 :=
  by by_cases h : P <;> simp [h]
#align ite_mul_one ite_mul_one
#align ite_add_zero ite_add_zero
-/

#print ite_one_mul /-
@[to_additive]
theorem ite_one_mul {P : Prop} [Decidable P] {a b : M} : ite P 1 (a * b) = ite P 1 a * ite P 1 b :=
  by by_cases h : P <;> simp [h]
#align ite_one_mul ite_one_mul
#align ite_zero_add ite_zero_add
-/

#print eq_one_iff_eq_one_of_mul_eq_one /-
@[to_additive]
theorem eq_one_iff_eq_one_of_mul_eq_one {a b : M} (h : a * b = 1) : a = 1 ↔ b = 1 := by
  constructor <;> · rintro rfl; simpa using h
#align eq_one_iff_eq_one_of_mul_eq_one eq_one_iff_eq_one_of_mul_eq_one
#align eq_zero_iff_eq_zero_of_add_eq_zero eq_zero_iff_eq_zero_of_add_eq_zero
-/

#print one_mul_eq_id /-
@[to_additive]
theorem one_mul_eq_id : (· * ·) (1 : M) = id :=
  funext one_mul
#align one_mul_eq_id one_mul_eq_id
#align zero_add_eq_id zero_add_eq_id
-/

#print mul_one_eq_id /-
@[to_additive]
theorem mul_one_eq_id : (· * (1 : M)) = id :=
  funext mul_one
#align mul_one_eq_id mul_one_eq_id
#align add_zero_eq_id add_zero_eq_id
-/

end MulOneClass

section CommSemigroup

variable [CommSemigroup G]

#print mul_left_comm /-
@[no_rsimp, to_additive]
theorem mul_left_comm : ∀ a b c : G, a * (b * c) = b * (a * c) :=
  left_comm Mul.mul mul_comm mul_assoc
#align mul_left_comm mul_left_comm
#align add_left_comm add_left_comm
-/

#print mul_right_comm /-
@[to_additive]
theorem mul_right_comm : ∀ a b c : G, a * b * c = a * c * b :=
  right_comm Mul.mul mul_comm mul_assoc
#align mul_right_comm mul_right_comm
#align add_right_comm add_right_comm
-/

#print mul_mul_mul_comm /-
@[to_additive]
theorem mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  simp only [mul_left_comm, mul_assoc]
#align mul_mul_mul_comm mul_mul_mul_comm
#align add_add_add_comm add_add_add_comm
-/

#print mul_rotate /-
@[to_additive]
theorem mul_rotate (a b c : G) : a * b * c = b * c * a := by simp only [mul_left_comm, mul_comm]
#align mul_rotate mul_rotate
#align add_rotate add_rotate
-/

#print mul_rotate' /-
@[to_additive]
theorem mul_rotate' (a b c : G) : a * (b * c) = b * (c * a) := by
  simp only [mul_left_comm, mul_comm]
#align mul_rotate' mul_rotate'
#align add_rotate' add_rotate'
-/

end CommSemigroup

section AddCommSemigroup

variable {M : Type u} [AddCommSemigroup M]

#print bit0_add /-
theorem bit0_add (a b : M) : bit0 (a + b) = bit0 a + bit0 b :=
  add_add_add_comm _ _ _ _
#align bit0_add bit0_add
-/

#print bit1_add /-
theorem bit1_add [One M] (a b : M) : bit1 (a + b) = bit0 a + bit1 b :=
  (congr_arg (· + (1 : M)) <| bit0_add a b : _).trans (add_assoc _ _ _)
#align bit1_add bit1_add
-/

#print bit1_add' /-
theorem bit1_add' [One M] (a b : M) : bit1 (a + b) = bit1 a + bit0 b := by
  rw [add_comm, bit1_add, add_comm]
#align bit1_add' bit1_add'
-/

end AddCommSemigroup

attribute [local simp] mul_assoc sub_eq_add_neg

section AddMonoid

variable {M : Type u} [AddMonoid M] {a b c : M}

#print bit0_zero /-
@[simp]
theorem bit0_zero : bit0 (0 : M) = 0 :=
  add_zero _
#align bit0_zero bit0_zero
-/

#print bit1_zero /-
@[simp]
theorem bit1_zero [One M] : bit1 (0 : M) = 1 := by rw [bit1, bit0_zero, zero_add]
#align bit1_zero bit1_zero
-/

end AddMonoid

section CommMonoid

variable {M : Type u} [CommMonoid M] {x y z : M}

#print inv_unique /-
@[to_additive]
theorem inv_unique (hy : x * y = 1) (hz : x * z = 1) : y = z :=
  left_inv_eq_right_inv (trans (mul_comm _ _) hy) hz
#align inv_unique inv_unique
#align neg_unique neg_unique
-/

end CommMonoid

section LeftCancelMonoid

variable {M : Type u} [LeftCancelMonoid M] {a b : M}

#print mul_right_eq_self /-
@[simp, to_additive]
theorem mul_right_eq_self : a * b = a ↔ b = 1 :=
  calc
    a * b = a ↔ a * b = a * 1 := by rw [mul_one]
    _ ↔ b = 1 := mul_left_cancel_iff
#align mul_right_eq_self mul_right_eq_self
#align add_right_eq_self add_right_eq_self
-/

#print self_eq_mul_right /-
@[simp, to_additive]
theorem self_eq_mul_right : a = a * b ↔ b = 1 :=
  eq_comm.trans mul_right_eq_self
#align self_eq_mul_right self_eq_mul_right
#align self_eq_add_right self_eq_add_right
-/

#print mul_right_ne_self /-
@[to_additive]
theorem mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 :=
  mul_right_eq_self.Not
#align mul_right_ne_self mul_right_ne_self
#align add_right_ne_self add_right_ne_self
-/

#print self_ne_mul_right /-
@[to_additive]
theorem self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 :=
  self_eq_mul_right.Not
#align self_ne_mul_right self_ne_mul_right
#align self_ne_add_right self_ne_add_right
-/

end LeftCancelMonoid

section RightCancelMonoid

variable {M : Type u} [RightCancelMonoid M] {a b : M}

#print mul_left_eq_self /-
@[simp, to_additive]
theorem mul_left_eq_self : a * b = b ↔ a = 1 :=
  calc
    a * b = b ↔ a * b = 1 * b := by rw [one_mul]
    _ ↔ a = 1 := mul_right_cancel_iff
#align mul_left_eq_self mul_left_eq_self
#align add_left_eq_self add_left_eq_self
-/

#print self_eq_mul_left /-
@[simp, to_additive]
theorem self_eq_mul_left : b = a * b ↔ a = 1 :=
  eq_comm.trans mul_left_eq_self
#align self_eq_mul_left self_eq_mul_left
#align self_eq_add_left self_eq_add_left
-/

#print mul_left_ne_self /-
@[to_additive]
theorem mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 :=
  mul_left_eq_self.Not
#align mul_left_ne_self mul_left_ne_self
#align add_left_ne_self add_left_ne_self
-/

#print self_ne_mul_left /-
@[to_additive]
theorem self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 :=
  self_eq_mul_left.Not
#align self_ne_mul_left self_ne_mul_left
#align self_ne_add_left self_ne_add_left
-/

end RightCancelMonoid

section InvolutiveInv

variable [InvolutiveInv G] {a b : G}

#print inv_involutive /-
@[simp, to_additive]
theorem inv_involutive : Function.Involutive (Inv.inv : G → G) :=
  inv_inv
#align inv_involutive inv_involutive
#align neg_involutive neg_involutive
-/

#print inv_surjective /-
@[simp, to_additive]
theorem inv_surjective : Function.Surjective (Inv.inv : G → G) :=
  inv_involutive.Surjective
#align inv_surjective inv_surjective
#align neg_surjective neg_surjective
-/

#print inv_injective /-
@[to_additive]
theorem inv_injective : Function.Injective (Inv.inv : G → G) :=
  inv_involutive.Injective
#align inv_injective inv_injective
#align neg_injective neg_injective
-/

#print inv_inj /-
@[simp, to_additive]
theorem inv_inj {a b : G} : a⁻¹ = b⁻¹ ↔ a = b :=
  inv_injective.eq_iff
#align inv_inj inv_inj
#align neg_inj neg_inj
-/

#print inv_eq_iff_eq_inv /-
@[to_additive]
theorem inv_eq_iff_eq_inv : a⁻¹ = b ↔ a = b⁻¹ :=
  ⟨fun h => h ▸ (inv_inv a).symm, fun h => h.symm ▸ inv_inv b⟩
#align inv_eq_iff_eq_inv inv_eq_iff_eq_inv
#align neg_eq_iff_eq_neg neg_eq_iff_eq_neg
-/

variable (G)

#print inv_comp_inv /-
@[simp, to_additive]
theorem inv_comp_inv : Inv.inv ∘ Inv.inv = @id G :=
  inv_involutive.comp_self
#align inv_comp_inv inv_comp_inv
#align neg_comp_neg neg_comp_neg
-/

#print leftInverse_inv /-
@[to_additive]
theorem leftInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv
#align left_inverse_inv leftInverse_inv
#align left_inverse_neg leftInverse_neg
-/

#print rightInverse_inv /-
@[to_additive]
theorem rightInverse_inv : LeftInverse (fun a : G => a⁻¹) fun a => a⁻¹ :=
  inv_inv
#align right_inverse_inv rightInverse_inv
#align right_inverse_neg rightInverse_neg
-/

end InvolutiveInv

section DivInvMonoid

variable [DivInvMonoid G] {a b c : G}

#print inv_eq_one_div /-
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem inv_eq_one_div (x : G) : x⁻¹ = 1 / x := by rw [div_eq_mul_inv, one_mul]
#align inv_eq_one_div inv_eq_one_div
#align neg_eq_zero_sub neg_eq_zero_sub
-/

#print mul_one_div /-
@[to_additive]
theorem mul_one_div (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]
#align mul_one_div mul_one_div
#align add_zero_sub add_zero_sub
-/

#print mul_div_assoc /-
@[to_additive]
theorem mul_div_assoc (a b c : G) : a * b / c = a * (b / c) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc _ _ _]
#align mul_div_assoc mul_div_assoc
#align add_sub_assoc add_sub_assoc
-/

#print mul_div_assoc' /-
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem mul_div_assoc' (a b c : G) : a * (b / c) = a * b / c :=
  (mul_div_assoc _ _ _).symm
#align mul_div_assoc' mul_div_assoc'
#align add_sub_assoc' add_sub_assoc'
-/

#print one_div /-
@[simp, to_additive]
theorem one_div (a : G) : 1 / a = a⁻¹ :=
  (inv_eq_one_div a).symm
#align one_div one_div
#align zero_sub zero_sub
-/

#print mul_div /-
@[to_additive]
theorem mul_div (a b c : G) : a * (b / c) = a * b / c := by simp only [mul_assoc, div_eq_mul_inv]
#align mul_div mul_div
#align add_sub add_sub
-/

#print div_eq_mul_one_div /-
@[to_additive]
theorem div_eq_mul_one_div (a b : G) : a / b = a * (1 / b) := by rw [div_eq_mul_inv, one_div]
#align div_eq_mul_one_div div_eq_mul_one_div
#align sub_eq_add_zero_sub sub_eq_add_zero_sub
-/

end DivInvMonoid

section DivInvOneMonoid

variable [DivInvOneMonoid G]

#print div_one /-
@[simp, to_additive]
theorem div_one (a : G) : a / 1 = a := by simp [div_eq_mul_inv]
#align div_one div_one
#align sub_zero sub_zero
-/

#print one_div_one /-
@[to_additive]
theorem one_div_one : (1 : G) / 1 = 1 :=
  div_one _
#align one_div_one one_div_one
#align zero_sub_zero zero_sub_zero
-/

end DivInvOneMonoid

section DivisionMonoid

variable [DivisionMonoid α] {a b c : α}

attribute [local simp] mul_assoc div_eq_mul_inv

#print inv_eq_of_mul_eq_one_left /-
@[to_additive]
theorem inv_eq_of_mul_eq_one_left (h : a * b = 1) : b⁻¹ = a := by
  rw [← inv_eq_of_mul_eq_one_right h, inv_inv]
#align inv_eq_of_mul_eq_one_left inv_eq_of_mul_eq_one_left
#align neg_eq_of_add_eq_zero_left neg_eq_of_add_eq_zero_left
-/

#print eq_inv_of_mul_eq_one_left /-
@[to_additive]
theorem eq_inv_of_mul_eq_one_left (h : a * b = 1) : a = b⁻¹ :=
  (inv_eq_of_mul_eq_one_left h).symm
#align eq_inv_of_mul_eq_one_left eq_inv_of_mul_eq_one_left
#align eq_neg_of_add_eq_zero_left eq_neg_of_add_eq_zero_left
-/

#print eq_inv_of_mul_eq_one_right /-
@[to_additive]
theorem eq_inv_of_mul_eq_one_right (h : a * b = 1) : b = a⁻¹ :=
  (inv_eq_of_mul_eq_one_right h).symm
#align eq_inv_of_mul_eq_one_right eq_inv_of_mul_eq_one_right
#align eq_neg_of_add_eq_zero_right eq_neg_of_add_eq_zero_right
-/

#print eq_one_div_of_mul_eq_one_left /-
@[to_additive]
theorem eq_one_div_of_mul_eq_one_left (h : b * a = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_left h, one_div]
#align eq_one_div_of_mul_eq_one_left eq_one_div_of_mul_eq_one_left
#align eq_zero_sub_of_add_eq_zero_left eq_zero_sub_of_add_eq_zero_left
-/

#print eq_one_div_of_mul_eq_one_right /-
@[to_additive]
theorem eq_one_div_of_mul_eq_one_right (h : a * b = 1) : b = 1 / a := by
  rw [eq_inv_of_mul_eq_one_right h, one_div]
#align eq_one_div_of_mul_eq_one_right eq_one_div_of_mul_eq_one_right
#align eq_zero_sub_of_add_eq_zero_right eq_zero_sub_of_add_eq_zero_right
-/

#print eq_of_div_eq_one /-
@[to_additive]
theorem eq_of_div_eq_one (h : a / b = 1) : a = b :=
  inv_injective <| inv_eq_of_mul_eq_one_right <| by rwa [← div_eq_mul_inv]
#align eq_of_div_eq_one eq_of_div_eq_one
#align eq_of_sub_eq_zero eq_of_sub_eq_zero
-/

#print div_ne_one_of_ne /-
@[to_additive]
theorem div_ne_one_of_ne : a ≠ b → a / b ≠ 1 :=
  mt eq_of_div_eq_one
#align div_ne_one_of_ne div_ne_one_of_ne
#align sub_ne_zero_of_ne sub_ne_zero_of_ne
-/

variable (a b c)

#print one_div_mul_one_div_rev /-
@[to_additive]
theorem one_div_mul_one_div_rev : 1 / a * (1 / b) = 1 / (b * a) := by simp
#align one_div_mul_one_div_rev one_div_mul_one_div_rev
#align zero_sub_add_zero_sub_rev zero_sub_add_zero_sub_rev
-/

#print inv_div_left /-
@[to_additive]
theorem inv_div_left : a⁻¹ / b = (b * a)⁻¹ := by simp
#align inv_div_left inv_div_left
#align neg_sub_left neg_sub_left
-/

#print inv_div /-
@[simp, to_additive]
theorem inv_div : (a / b)⁻¹ = b / a := by simp
#align inv_div inv_div
#align neg_sub neg_sub
-/

#print one_div_div /-
@[simp, to_additive]
theorem one_div_div : 1 / (a / b) = b / a := by simp
#align one_div_div one_div_div
#align zero_sub_sub zero_sub_sub
-/

#print one_div_one_div /-
@[to_additive]
theorem one_div_one_div : 1 / (1 / a) = a := by simp
#align one_div_one_div one_div_one_div
#align zero_sub_zero_sub zero_sub_zero_sub
-/

#print DivisionMonoid.toDivInvOneMonoid /-
@[to_additive SubtractionMonoid.toSubNegZeroMonoid]
instance (priority := 100) DivisionMonoid.toDivInvOneMonoid : DivInvOneMonoid α :=
  { DivisionMonoid.toDivInvMonoid α with
    inv_one := by simpa only [one_div, inv_inv] using (inv_div (1 : α) 1).symm }
#align division_monoid.to_div_inv_one_monoid DivisionMonoid.toDivInvOneMonoid
#align subtraction_monoid.to_sub_neg_zero_monoid SubtractionMonoid.toSubNegZeroMonoid
-/

variable {a b c}

#print inv_eq_one /-
@[simp, to_additive]
theorem inv_eq_one : a⁻¹ = 1 ↔ a = 1 :=
  inv_injective.eq_iff' inv_one
#align inv_eq_one inv_eq_one
#align neg_eq_zero neg_eq_zero
-/

#print one_eq_inv /-
@[simp, to_additive]
theorem one_eq_inv : 1 = a⁻¹ ↔ a = 1 :=
  eq_comm.trans inv_eq_one
#align one_eq_inv one_eq_inv
#align zero_eq_neg zero_eq_neg
-/

#print inv_ne_one /-
@[to_additive]
theorem inv_ne_one : a⁻¹ ≠ 1 ↔ a ≠ 1 :=
  inv_eq_one.Not
#align inv_ne_one inv_ne_one
#align neg_ne_zero neg_ne_zero
-/

#print eq_of_one_div_eq_one_div /-
@[to_additive]
theorem eq_of_one_div_eq_one_div (h : 1 / a = 1 / b) : a = b := by
  rw [← one_div_one_div a, h, one_div_one_div]
#align eq_of_one_div_eq_one_div eq_of_one_div_eq_one_div
#align eq_of_zero_sub_eq_zero_sub eq_of_zero_sub_eq_zero_sub
-/

variable (a b c)

#print div_div_eq_mul_div /-
-- The attributes are out of order on purpose
@[to_additive, field_simps]
theorem div_div_eq_mul_div : a / (b / c) = a * c / b := by simp
#align div_div_eq_mul_div div_div_eq_mul_div
#align sub_sub_eq_add_sub sub_sub_eq_add_sub
-/

#print div_inv_eq_mul /-
@[simp, to_additive]
theorem div_inv_eq_mul : a / b⁻¹ = a * b := by simp
#align div_inv_eq_mul div_inv_eq_mul
#align sub_neg_eq_add sub_neg_eq_add
-/

#print div_mul_eq_div_div_swap /-
@[to_additive]
theorem div_mul_eq_div_div_swap : a / (b * c) = a / c / b := by
  simp only [mul_assoc, mul_inv_rev, div_eq_mul_inv]
#align div_mul_eq_div_div_swap div_mul_eq_div_div_swap
#align sub_add_eq_sub_sub_swap sub_add_eq_sub_sub_swap
-/

end DivisionMonoid

#print bit0_neg /-
theorem bit0_neg [SubtractionMonoid α] (a : α) : bit0 (-a) = -bit0 a :=
  (neg_add_rev _ _).symm
#align bit0_neg bit0_neg
-/

section DivisionCommMonoid

variable [DivisionCommMonoid α] (a b c d : α)

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

#print mul_inv /-
@[to_additive neg_add]
theorem mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by simp
#align mul_inv mul_inv
#align neg_add neg_add
-/

#print inv_div' /-
@[to_additive]
theorem inv_div' : (a / b)⁻¹ = a⁻¹ / b⁻¹ := by simp
#align inv_div' inv_div'
#align neg_sub' neg_sub'
-/

#print div_eq_inv_mul /-
@[to_additive]
theorem div_eq_inv_mul : a / b = b⁻¹ * a := by simp
#align div_eq_inv_mul div_eq_inv_mul
#align sub_eq_neg_add sub_eq_neg_add
-/

#print inv_mul_eq_div /-
@[to_additive]
theorem inv_mul_eq_div : a⁻¹ * b = b / a := by simp
#align inv_mul_eq_div inv_mul_eq_div
#align neg_add_eq_sub neg_add_eq_sub
-/

#print inv_mul' /-
@[to_additive]
theorem inv_mul' : (a * b)⁻¹ = a⁻¹ / b := by simp
#align inv_mul' inv_mul'
#align neg_add' neg_add'
-/

#print inv_div_inv /-
@[simp, to_additive]
theorem inv_div_inv : a⁻¹ / b⁻¹ = b / a := by simp
#align inv_div_inv inv_div_inv
#align neg_sub_neg neg_sub_neg
-/

#print inv_inv_div_inv /-
@[to_additive]
theorem inv_inv_div_inv : (a⁻¹ / b⁻¹)⁻¹ = a / b := by simp
#align inv_inv_div_inv inv_inv_div_inv
#align neg_neg_sub_neg neg_neg_sub_neg
-/

#print one_div_mul_one_div /-
@[to_additive]
theorem one_div_mul_one_div : 1 / a * (1 / b) = 1 / (a * b) := by simp
#align one_div_mul_one_div one_div_mul_one_div
#align zero_sub_add_zero_sub zero_sub_add_zero_sub
-/

#print div_right_comm /-
@[to_additive]
theorem div_right_comm : a / b / c = a / c / b := by simp
#align div_right_comm div_right_comm
#align sub_right_comm sub_right_comm
-/

#print div_div /-
@[to_additive, field_simps]
theorem div_div : a / b / c = a / (b * c) := by simp
#align div_div div_div
#align sub_sub sub_sub
-/

#print div_mul /-
@[to_additive]
theorem div_mul : a / b * c = a / (b / c) := by simp
#align div_mul div_mul
#align sub_add sub_add
-/

#print mul_div_left_comm /-
@[to_additive]
theorem mul_div_left_comm : a * (b / c) = b * (a / c) := by simp
#align mul_div_left_comm mul_div_left_comm
#align add_sub_left_comm add_sub_left_comm
-/

#print mul_div_right_comm /-
@[to_additive]
theorem mul_div_right_comm : a * b / c = a / c * b := by simp
#align mul_div_right_comm mul_div_right_comm
#align add_sub_right_comm add_sub_right_comm
-/

#print div_mul_eq_div_div /-
@[to_additive]
theorem div_mul_eq_div_div : a / (b * c) = a / b / c := by simp
#align div_mul_eq_div_div div_mul_eq_div_div
#align sub_add_eq_sub_sub sub_add_eq_sub_sub
-/

#print div_mul_eq_mul_div /-
@[to_additive, field_simps]
theorem div_mul_eq_mul_div : a / b * c = a * c / b := by simp
#align div_mul_eq_mul_div div_mul_eq_mul_div
#align sub_add_eq_add_sub sub_add_eq_add_sub
-/

#print mul_comm_div /-
@[to_additive]
theorem mul_comm_div : a / b * c = a * (c / b) := by simp
#align mul_comm_div mul_comm_div
#align add_comm_sub add_comm_sub
-/

#print div_mul_comm /-
@[to_additive]
theorem div_mul_comm : a / b * c = c / b * a := by simp
#align div_mul_comm div_mul_comm
#align sub_add_comm sub_add_comm
-/

#print div_mul_eq_div_mul_one_div /-
@[to_additive]
theorem div_mul_eq_div_mul_one_div : a / (b * c) = a / b * (1 / c) := by simp
#align div_mul_eq_div_mul_one_div div_mul_eq_div_mul_one_div
#align sub_add_eq_sub_add_zero_sub sub_add_eq_sub_add_zero_sub
-/

#print div_div_div_eq /-
@[to_additive]
theorem div_div_div_eq : a / b / (c / d) = a * d / (b * c) := by simp
#align div_div_div_eq div_div_div_eq
#align sub_sub_sub_eq sub_sub_sub_eq
-/

#print div_div_div_comm /-
@[to_additive]
theorem div_div_div_comm : a / b / (c / d) = a / c / (b / d) := by simp
#align div_div_div_comm div_div_div_comm
#align sub_sub_sub_comm sub_sub_sub_comm
-/

#print div_mul_div_comm /-
@[to_additive]
theorem div_mul_div_comm : a / b * (c / d) = a * c / (b * d) := by simp
#align div_mul_div_comm div_mul_div_comm
#align sub_add_sub_comm sub_add_sub_comm
-/

#print mul_div_mul_comm /-
@[to_additive]
theorem mul_div_mul_comm : a * b / (c * d) = a / c * (b / d) := by simp
#align mul_div_mul_comm mul_div_mul_comm
#align add_sub_add_comm add_sub_add_comm
-/

end DivisionCommMonoid

section Group

variable [Group G] {a b c d : G}

#print div_eq_inv_self /-
@[simp, to_additive]
theorem div_eq_inv_self : a / b = b⁻¹ ↔ a = 1 := by rw [div_eq_mul_inv, mul_left_eq_self]
#align div_eq_inv_self div_eq_inv_self
#align sub_eq_neg_self sub_eq_neg_self
-/

#print mul_left_surjective /-
@[to_additive]
theorem mul_left_surjective (a : G) : Function.Surjective ((· * ·) a) := fun x =>
  ⟨a⁻¹ * x, mul_inv_cancel_left a x⟩
#align mul_left_surjective mul_left_surjective
#align add_left_surjective add_left_surjective
-/

#print mul_right_surjective /-
@[to_additive]
theorem mul_right_surjective (a : G) : Function.Surjective fun x => x * a := fun x =>
  ⟨x * a⁻¹, inv_mul_cancel_right x a⟩
#align mul_right_surjective mul_right_surjective
#align add_right_surjective add_right_surjective
-/

#print eq_mul_inv_of_mul_eq /-
@[to_additive]
theorem eq_mul_inv_of_mul_eq (h : a * c = b) : a = b * c⁻¹ := by simp [h.symm]
#align eq_mul_inv_of_mul_eq eq_mul_inv_of_mul_eq
#align eq_add_neg_of_add_eq eq_add_neg_of_add_eq
-/

#print eq_inv_mul_of_mul_eq /-
@[to_additive]
theorem eq_inv_mul_of_mul_eq (h : b * a = c) : a = b⁻¹ * c := by simp [h.symm]
#align eq_inv_mul_of_mul_eq eq_inv_mul_of_mul_eq
#align eq_neg_add_of_add_eq eq_neg_add_of_add_eq
-/

#print inv_mul_eq_of_eq_mul /-
@[to_additive]
theorem inv_mul_eq_of_eq_mul (h : b = a * c) : a⁻¹ * b = c := by simp [h]
#align inv_mul_eq_of_eq_mul inv_mul_eq_of_eq_mul
#align neg_add_eq_of_eq_add neg_add_eq_of_eq_add
-/

#print mul_inv_eq_of_eq_mul /-
@[to_additive]
theorem mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c := by simp [h]
#align mul_inv_eq_of_eq_mul mul_inv_eq_of_eq_mul
#align add_neg_eq_of_eq_add add_neg_eq_of_eq_add
-/

#print eq_mul_of_mul_inv_eq /-
@[to_additive]
theorem eq_mul_of_mul_inv_eq (h : a * c⁻¹ = b) : a = b * c := by simp [h.symm]
#align eq_mul_of_mul_inv_eq eq_mul_of_mul_inv_eq
#align eq_add_of_add_neg_eq eq_add_of_add_neg_eq
-/

#print eq_mul_of_inv_mul_eq /-
@[to_additive]
theorem eq_mul_of_inv_mul_eq (h : b⁻¹ * a = c) : a = b * c := by simp [h.symm, mul_inv_cancel_left]
#align eq_mul_of_inv_mul_eq eq_mul_of_inv_mul_eq
#align eq_add_of_neg_add_eq eq_add_of_neg_add_eq
-/

#print mul_eq_of_eq_inv_mul /-
@[to_additive]
theorem mul_eq_of_eq_inv_mul (h : b = a⁻¹ * c) : a * b = c := by rw [h, mul_inv_cancel_left]
#align mul_eq_of_eq_inv_mul mul_eq_of_eq_inv_mul
#align add_eq_of_eq_neg_add add_eq_of_eq_neg_add
-/

#print mul_eq_of_eq_mul_inv /-
@[to_additive]
theorem mul_eq_of_eq_mul_inv (h : a = c * b⁻¹) : a * b = c := by simp [h]
#align mul_eq_of_eq_mul_inv mul_eq_of_eq_mul_inv
#align add_eq_of_eq_add_neg add_eq_of_eq_add_neg
-/

#print mul_eq_one_iff_eq_inv /-
@[to_additive]
theorem mul_eq_one_iff_eq_inv : a * b = 1 ↔ a = b⁻¹ :=
  ⟨eq_inv_of_mul_eq_one_left, fun h => by rw [h, mul_left_inv]⟩
#align mul_eq_one_iff_eq_inv mul_eq_one_iff_eq_inv
#align add_eq_zero_iff_eq_neg add_eq_zero_iff_eq_neg
-/

#print mul_eq_one_iff_inv_eq /-
@[to_additive]
theorem mul_eq_one_iff_inv_eq : a * b = 1 ↔ a⁻¹ = b := by
  rw [mul_eq_one_iff_eq_inv, inv_eq_iff_eq_inv]
#align mul_eq_one_iff_inv_eq mul_eq_one_iff_inv_eq
#align add_eq_zero_iff_neg_eq add_eq_zero_iff_neg_eq
-/

#print eq_inv_iff_mul_eq_one /-
@[to_additive]
theorem eq_inv_iff_mul_eq_one : a = b⁻¹ ↔ a * b = 1 :=
  mul_eq_one_iff_eq_inv.symm
#align eq_inv_iff_mul_eq_one eq_inv_iff_mul_eq_one
#align eq_neg_iff_add_eq_zero eq_neg_iff_add_eq_zero
-/

#print inv_eq_iff_mul_eq_one /-
@[to_additive]
theorem inv_eq_iff_mul_eq_one : a⁻¹ = b ↔ a * b = 1 :=
  mul_eq_one_iff_inv_eq.symm
#align inv_eq_iff_mul_eq_one inv_eq_iff_mul_eq_one
#align neg_eq_iff_add_eq_zero neg_eq_iff_add_eq_zero
-/

#print eq_mul_inv_iff_mul_eq /-
@[to_additive]
theorem eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b :=
  ⟨fun h => by rw [h, inv_mul_cancel_right], fun h => by rw [← h, mul_inv_cancel_right]⟩
#align eq_mul_inv_iff_mul_eq eq_mul_inv_iff_mul_eq
#align eq_add_neg_iff_add_eq eq_add_neg_iff_add_eq
-/

#print eq_inv_mul_iff_mul_eq /-
@[to_additive]
theorem eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c :=
  ⟨fun h => by rw [h, mul_inv_cancel_left], fun h => by rw [← h, inv_mul_cancel_left]⟩
#align eq_inv_mul_iff_mul_eq eq_inv_mul_iff_mul_eq
#align eq_neg_add_iff_add_eq eq_neg_add_iff_add_eq
-/

#print inv_mul_eq_iff_eq_mul /-
@[to_additive]
theorem inv_mul_eq_iff_eq_mul : a⁻¹ * b = c ↔ b = a * c :=
  ⟨fun h => by rw [← h, mul_inv_cancel_left], fun h => by rw [h, inv_mul_cancel_left]⟩
#align inv_mul_eq_iff_eq_mul inv_mul_eq_iff_eq_mul
#align neg_add_eq_iff_eq_add neg_add_eq_iff_eq_add
-/

#print mul_inv_eq_iff_eq_mul /-
@[to_additive]
theorem mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b :=
  ⟨fun h => by rw [← h, inv_mul_cancel_right], fun h => by rw [h, mul_inv_cancel_right]⟩
#align mul_inv_eq_iff_eq_mul mul_inv_eq_iff_eq_mul
#align add_neg_eq_iff_eq_add add_neg_eq_iff_eq_add
-/

#print mul_inv_eq_one /-
@[to_additive]
theorem mul_inv_eq_one : a * b⁻¹ = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inv]
#align mul_inv_eq_one mul_inv_eq_one
#align add_neg_eq_zero add_neg_eq_zero
-/

#print inv_mul_eq_one /-
@[to_additive]
theorem inv_mul_eq_one : a⁻¹ * b = 1 ↔ a = b := by rw [mul_eq_one_iff_eq_inv, inv_inj]
#align inv_mul_eq_one inv_mul_eq_one
#align neg_add_eq_zero neg_add_eq_zero
-/

#print div_left_injective /-
@[to_additive]
theorem div_left_injective : Function.Injective fun a => a / b := by
  simpa only [div_eq_mul_inv] using fun a a' h => mul_left_injective b⁻¹ h
#align div_left_injective div_left_injective
#align sub_left_injective sub_left_injective
-/

#print div_right_injective /-
@[to_additive]
theorem div_right_injective : Function.Injective fun a => b / a := by
  simpa only [div_eq_mul_inv] using fun a a' h => inv_injective (mul_right_injective b h)
#align div_right_injective div_right_injective
#align sub_right_injective sub_right_injective
-/

#print div_mul_cancel' /-
@[simp, to_additive sub_add_cancel]
theorem div_mul_cancel' (a b : G) : a / b * b = a := by
  rw [div_eq_mul_inv, inv_mul_cancel_right a b]
#align div_mul_cancel' div_mul_cancel'
#align sub_add_cancel sub_add_cancel
-/

#print div_self' /-
@[simp, to_additive sub_self]
theorem div_self' (a : G) : a / a = 1 := by rw [div_eq_mul_inv, mul_right_inv a]
#align div_self' div_self'
#align sub_self sub_self
-/

#print mul_div_cancel'' /-
@[simp, to_additive add_sub_cancel]
theorem mul_div_cancel'' (a b : G) : a * b / b = a := by
  rw [div_eq_mul_inv, mul_inv_cancel_right a b]
#align mul_div_cancel'' mul_div_cancel''
#align add_sub_cancel add_sub_cancel
-/

#print div_mul_cancel''' /-
@[simp, to_additive sub_add_cancel'']
theorem div_mul_cancel''' (a b : G) : a / (b * a) = b⁻¹ := by rw [← inv_div, mul_div_cancel'']
#align div_mul_cancel''' div_mul_cancel'''
#align sub_add_cancel'' sub_add_cancel''
-/

#print mul_div_mul_right_eq_div /-
@[simp, to_additive]
theorem mul_div_mul_right_eq_div (a b c : G) : a * c / (b * c) = a / b := by
  rw [div_mul_eq_div_div_swap] <;> simp only [mul_left_inj, eq_self_iff_true, mul_div_cancel'']
#align mul_div_mul_right_eq_div mul_div_mul_right_eq_div
#align add_sub_add_right_eq_sub add_sub_add_right_eq_sub
-/

#print eq_div_of_mul_eq' /-
@[to_additive eq_sub_of_add_eq]
theorem eq_div_of_mul_eq' (h : a * c = b) : a = b / c := by simp [← h]
#align eq_div_of_mul_eq' eq_div_of_mul_eq'
#align eq_sub_of_add_eq eq_sub_of_add_eq
-/

#print div_eq_of_eq_mul'' /-
@[to_additive sub_eq_of_eq_add]
theorem div_eq_of_eq_mul'' (h : a = c * b) : a / b = c := by simp [h]
#align div_eq_of_eq_mul'' div_eq_of_eq_mul''
#align sub_eq_of_eq_add sub_eq_of_eq_add
-/

#print eq_mul_of_div_eq /-
@[to_additive]
theorem eq_mul_of_div_eq (h : a / c = b) : a = b * c := by simp [← h]
#align eq_mul_of_div_eq eq_mul_of_div_eq
#align eq_add_of_sub_eq eq_add_of_sub_eq
-/

#print mul_eq_of_eq_div /-
@[to_additive]
theorem mul_eq_of_eq_div (h : a = c / b) : a * b = c := by simp [h]
#align mul_eq_of_eq_div mul_eq_of_eq_div
#align add_eq_of_eq_sub add_eq_of_eq_sub
-/

#print div_right_inj /-
@[simp, to_additive]
theorem div_right_inj : a / b = a / c ↔ b = c :=
  div_right_injective.eq_iff
#align div_right_inj div_right_inj
#align sub_right_inj sub_right_inj
-/

#print div_left_inj /-
@[simp, to_additive]
theorem div_left_inj : b / a = c / a ↔ b = c := by rw [div_eq_mul_inv, div_eq_mul_inv];
  exact mul_left_inj _
#align div_left_inj div_left_inj
#align sub_left_inj sub_left_inj
-/

#print div_mul_div_cancel' /-
@[simp, to_additive sub_add_sub_cancel]
theorem div_mul_div_cancel' (a b c : G) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel']
#align div_mul_div_cancel' div_mul_div_cancel'
#align sub_add_sub_cancel sub_add_sub_cancel
-/

#print div_div_div_cancel_right' /-
@[simp, to_additive sub_sub_sub_cancel_right]
theorem div_div_div_cancel_right' (a b c : G) : a / c / (b / c) = a / b := by
  rw [← inv_div c b, div_inv_eq_mul, div_mul_div_cancel']
#align div_div_div_cancel_right' div_div_div_cancel_right'
#align sub_sub_sub_cancel_right sub_sub_sub_cancel_right
-/

#print div_eq_one /-
@[to_additive]
theorem div_eq_one : a / b = 1 ↔ a = b :=
  ⟨eq_of_div_eq_one, fun h => by rw [h, div_self']⟩
#align div_eq_one div_eq_one
#align sub_eq_zero sub_eq_zero
-/

alias div_eq_one ↔ _ div_eq_one_of_eq
#align div_eq_one_of_eq div_eq_one_of_eq

alias sub_eq_zero ↔ _ sub_eq_zero_of_eq
#align sub_eq_zero_of_eq sub_eq_zero_of_eq

#print div_ne_one /-
@[to_additive]
theorem div_ne_one : a / b ≠ 1 ↔ a ≠ b :=
  not_congr div_eq_one
#align div_ne_one div_ne_one
#align sub_ne_zero sub_ne_zero
-/

#print div_eq_self /-
@[simp, to_additive]
theorem div_eq_self : a / b = a ↔ b = 1 := by rw [div_eq_mul_inv, mul_right_eq_self, inv_eq_one]
#align div_eq_self div_eq_self
#align sub_eq_self sub_eq_self
-/

#print eq_div_iff_mul_eq' /-
@[to_additive eq_sub_iff_add_eq]
theorem eq_div_iff_mul_eq' : a = b / c ↔ a * c = b := by rw [div_eq_mul_inv, eq_mul_inv_iff_mul_eq]
#align eq_div_iff_mul_eq' eq_div_iff_mul_eq'
#align eq_sub_iff_add_eq eq_sub_iff_add_eq
-/

#print div_eq_iff_eq_mul /-
@[to_additive]
theorem div_eq_iff_eq_mul : a / b = c ↔ a = c * b := by rw [div_eq_mul_inv, mul_inv_eq_iff_eq_mul]
#align div_eq_iff_eq_mul div_eq_iff_eq_mul
#align sub_eq_iff_eq_add sub_eq_iff_eq_add
-/

#print eq_iff_eq_of_div_eq_div /-
@[to_additive]
theorem eq_iff_eq_of_div_eq_div (H : a / b = c / d) : a = b ↔ c = d := by
  rw [← div_eq_one, H, div_eq_one]
#align eq_iff_eq_of_div_eq_div eq_iff_eq_of_div_eq_div
#align eq_iff_eq_of_sub_eq_sub eq_iff_eq_of_sub_eq_sub
-/

#print leftInverse_div_mul_left /-
@[to_additive]
theorem leftInverse_div_mul_left (c : G) : Function.LeftInverse (fun x => x / c) fun x => x * c :=
  fun x => mul_div_cancel'' x c
#align left_inverse_div_mul_left leftInverse_div_mul_left
#align left_inverse_sub_add_left leftInverse_sub_add_left
-/

#print leftInverse_mul_left_div /-
@[to_additive]
theorem leftInverse_mul_left_div (c : G) : Function.LeftInverse (fun x => x * c) fun x => x / c :=
  fun x => div_mul_cancel' x c
#align left_inverse_mul_left_div leftInverse_mul_left_div
#align left_inverse_add_left_sub leftInverse_add_left_sub
-/

#print leftInverse_mul_right_inv_mul /-
@[to_additive]
theorem leftInverse_mul_right_inv_mul (c : G) :
    Function.LeftInverse (fun x => c * x) fun x => c⁻¹ * x := fun x => mul_inv_cancel_left c x
#align left_inverse_mul_right_inv_mul leftInverse_mul_right_inv_mul
#align left_inverse_add_right_neg_add leftInverse_add_right_neg_add
-/

#print leftInverse_inv_mul_mul_right /-
@[to_additive]
theorem leftInverse_inv_mul_mul_right (c : G) :
    Function.LeftInverse (fun x => c⁻¹ * x) fun x => c * x := fun x => inv_mul_cancel_left c x
#align left_inverse_inv_mul_mul_right leftInverse_inv_mul_mul_right
#align left_inverse_neg_add_add_right leftInverse_neg_add_add_right
-/

#print exists_npow_eq_one_of_zpow_eq_one /-
@[to_additive]
theorem exists_npow_eq_one_of_zpow_eq_one {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  cases' n with n n
  · rw [zpow_ofNat] at h 
    refine' ⟨n, Nat.pos_of_ne_zero fun n0 => hn _, h⟩; rw [n0]; rfl
  · rw [zpow_negSucc, inv_eq_one] at h 
    refine' ⟨n + 1, n.succ_pos, h⟩
#align exists_npow_eq_one_of_zpow_eq_one exists_npow_eq_one_of_zpow_eq_one
#align exists_nsmul_eq_zero_of_zsmul_eq_zero exists_nsmul_eq_zero_of_zsmul_eq_zero
-/

end Group

section CommGroup

variable [CommGroup G] {a b c d : G}

attribute [local simp] mul_assoc mul_comm mul_left_comm div_eq_mul_inv

#print div_eq_of_eq_mul' /-
@[to_additive]
theorem div_eq_of_eq_mul' {a b c : G} (h : a = b * c) : a / b = c := by
  rw [h, div_eq_mul_inv, mul_comm, inv_mul_cancel_left]
#align div_eq_of_eq_mul' div_eq_of_eq_mul'
#align sub_eq_of_eq_add' sub_eq_of_eq_add'
-/

#print mul_div_mul_left_eq_div /-
@[simp, to_additive]
theorem mul_div_mul_left_eq_div (a b c : G) : c * a / (c * b) = a / b := by simp
#align mul_div_mul_left_eq_div mul_div_mul_left_eq_div
#align add_sub_add_left_eq_sub add_sub_add_left_eq_sub
-/

#print eq_div_of_mul_eq'' /-
@[to_additive eq_sub_of_add_eq']
theorem eq_div_of_mul_eq'' (h : c * a = b) : a = b / c := by simp [h.symm]
#align eq_div_of_mul_eq'' eq_div_of_mul_eq''
#align eq_sub_of_add_eq' eq_sub_of_add_eq'
-/

#print eq_mul_of_div_eq' /-
@[to_additive]
theorem eq_mul_of_div_eq' (h : a / b = c) : a = b * c := by simp [h.symm]
#align eq_mul_of_div_eq' eq_mul_of_div_eq'
#align eq_add_of_sub_eq' eq_add_of_sub_eq'
-/

#print mul_eq_of_eq_div' /-
@[to_additive]
theorem mul_eq_of_eq_div' (h : b = c / a) : a * b = c := by simp [h];
  rw [mul_comm c, mul_inv_cancel_left]
#align mul_eq_of_eq_div' mul_eq_of_eq_div'
#align add_eq_of_eq_sub' add_eq_of_eq_sub'
-/

#print div_div_self' /-
@[to_additive sub_sub_self]
theorem div_div_self' (a b : G) : a / (a / b) = b := by simpa using mul_inv_cancel_left a b
#align div_div_self' div_div_self'
#align sub_sub_self sub_sub_self
-/

#print div_eq_div_mul_div /-
@[to_additive]
theorem div_eq_div_mul_div (a b c : G) : a / b = c / b * (a / c) := by simp [mul_left_comm c]
#align div_eq_div_mul_div div_eq_div_mul_div
#align sub_eq_sub_add_sub sub_eq_sub_add_sub
-/

#print div_div_cancel /-
@[simp, to_additive]
theorem div_div_cancel (a b : G) : a / (a / b) = b :=
  div_div_self' a b
#align div_div_cancel div_div_cancel
#align sub_sub_cancel sub_sub_cancel
-/

#print div_div_cancel_left /-
@[simp, to_additive]
theorem div_div_cancel_left (a b : G) : a / b / a = b⁻¹ := by simp
#align div_div_cancel_left div_div_cancel_left
#align sub_sub_cancel_left sub_sub_cancel_left
-/

#print eq_div_iff_mul_eq'' /-
@[to_additive eq_sub_iff_add_eq']
theorem eq_div_iff_mul_eq'' : a = b / c ↔ c * a = b := by rw [eq_div_iff_mul_eq', mul_comm]
#align eq_div_iff_mul_eq'' eq_div_iff_mul_eq''
#align eq_sub_iff_add_eq' eq_sub_iff_add_eq'
-/

#print div_eq_iff_eq_mul' /-
@[to_additive]
theorem div_eq_iff_eq_mul' : a / b = c ↔ a = b * c := by rw [div_eq_iff_eq_mul, mul_comm]
#align div_eq_iff_eq_mul' div_eq_iff_eq_mul'
#align sub_eq_iff_eq_add' sub_eq_iff_eq_add'
-/

#print mul_div_cancel''' /-
@[simp, to_additive add_sub_cancel']
theorem mul_div_cancel''' (a b : G) : a * b / a = b := by rw [div_eq_inv_mul, inv_mul_cancel_left]
#align mul_div_cancel''' mul_div_cancel'''
#align add_sub_cancel' add_sub_cancel'
-/

#print mul_div_cancel'_right /-
@[simp, to_additive]
theorem mul_div_cancel'_right (a b : G) : a * (b / a) = b := by
  rw [← mul_div_assoc, mul_div_cancel''']
#align mul_div_cancel'_right mul_div_cancel'_right
#align add_sub_cancel'_right add_sub_cancel'_right
-/

#print div_mul_cancel'' /-
@[simp, to_additive sub_add_cancel']
theorem div_mul_cancel'' (a b : G) : a / (a * b) = b⁻¹ := by rw [← inv_div, mul_div_cancel''']
#align div_mul_cancel'' div_mul_cancel''
#align sub_add_cancel' sub_add_cancel'
-/

#print mul_mul_inv_cancel'_right /-
-- This lemma is in the `simp` set under the name `mul_inv_cancel_comm_assoc`,
-- along with the additive version `add_neg_cancel_comm_assoc`,
-- defined  in `algebra/group/commute`
@[to_additive]
theorem mul_mul_inv_cancel'_right (a b : G) : a * (b * a⁻¹) = b := by
  rw [← div_eq_mul_inv, mul_div_cancel'_right a b]
#align mul_mul_inv_cancel'_right mul_mul_inv_cancel'_right
#align add_add_neg_cancel'_right add_add_neg_cancel'_right
-/

#print mul_mul_div_cancel /-
@[simp, to_additive]
theorem mul_mul_div_cancel (a b c : G) : a * c * (b / c) = a * b := by
  rw [mul_assoc, mul_div_cancel'_right]
#align mul_mul_div_cancel mul_mul_div_cancel
#align add_add_sub_cancel add_add_sub_cancel
-/

#print div_mul_mul_cancel /-
@[simp, to_additive]
theorem div_mul_mul_cancel (a b c : G) : a / c * (b * c) = a * b := by
  rw [mul_left_comm, div_mul_cancel', mul_comm]
#align div_mul_mul_cancel div_mul_mul_cancel
#align sub_add_add_cancel sub_add_add_cancel
-/

#print div_mul_div_cancel'' /-
@[simp, to_additive sub_add_sub_cancel']
theorem div_mul_div_cancel'' (a b c : G) : a / b * (c / a) = c / b := by
  rw [mul_comm] <;> apply div_mul_div_cancel'
#align div_mul_div_cancel'' div_mul_div_cancel''
#align sub_add_sub_cancel' sub_add_sub_cancel'
-/

#print mul_div_div_cancel /-
@[simp, to_additive]
theorem mul_div_div_cancel (a b c : G) : a * b / (a / c) = b * c := by
  rw [← div_mul, mul_div_cancel''']
#align mul_div_div_cancel mul_div_div_cancel
#align add_sub_sub_cancel add_sub_sub_cancel
-/

#print div_div_div_cancel_left /-
@[simp, to_additive]
theorem div_div_div_cancel_left (a b c : G) : c / a / (c / b) = b / a := by
  rw [← inv_div b c, div_inv_eq_mul, mul_comm, div_mul_div_cancel']
#align div_div_div_cancel_left div_div_div_cancel_left
#align sub_sub_sub_cancel_left sub_sub_sub_cancel_left
-/

#print div_eq_div_iff_mul_eq_mul /-
@[to_additive]
theorem div_eq_div_iff_mul_eq_mul : a / b = c / d ↔ a * d = c * b :=
  by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, eq_comm, div_eq_iff_eq_mul']
  simp only [mul_comm, eq_comm]
#align div_eq_div_iff_mul_eq_mul div_eq_div_iff_mul_eq_mul
#align sub_eq_sub_iff_add_eq_add sub_eq_sub_iff_add_eq_add
-/

#print div_eq_div_iff_div_eq_div /-
@[to_additive]
theorem div_eq_div_iff_div_eq_div : a / b = c / d ↔ a / c = b / d := by
  rw [div_eq_iff_eq_mul, div_mul_eq_mul_div, div_eq_iff_eq_mul', mul_div_assoc]
#align div_eq_div_iff_div_eq_div div_eq_div_iff_div_eq_div
#align sub_eq_sub_iff_sub_eq_sub sub_eq_sub_iff_sub_eq_sub
-/

end CommGroup

section SubtractionCommMonoid

variable {M : Type u} [SubtractionCommMonoid M]

theorem bit0_sub (a b : M) : bit0 (a - b) = bit0 a - bit0 b :=
  sub_add_sub_comm _ _ _ _
#align bit0_sub bit0_sub

theorem bit1_sub [One M] (a b : M) : bit1 (a - b) = bit1 a - bit0 b :=
  (congr_arg (· + (1 : M)) <| bit0_sub a b : _).trans <| sub_add_eq_add_sub _ _ _
#align bit1_sub bit1_sub

end SubtractionCommMonoid

section Multiplicative

variable [Monoid β] (p r : α → α → Prop) [IsTotal α r] (f : α → α → β)

#print multiplicative_of_symmetric_of_isTotal /-
@[to_additive additive_of_symmetric_of_isTotal]
theorem multiplicative_of_symmetric_of_isTotal (hsymm : Symmetric p)
    (hf_swap : ∀ {a b}, p a b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a b → p b c → p a c → f a c = f a b * f b c) {a b c : α}
    (pab : p a b) (pbc : p b c) (pac : p a c) : f a c = f a b * f b c :=
  by
  suffices ∀ {b c}, r b c → p a b → p b c → p a c → f a c = f a b * f b c
    by
    obtain rbc | rcb := total_of r b c
    · exact this rbc pab pbc pac
    · rw [this rcb pac (hsymm pbc) pab, mul_assoc, hf_swap (hsymm pbc), mul_one]
  intro b c rbc pab pbc pac
  obtain rab | rba := total_of r a b
  · exact hmul rab rbc pab pbc pac
  rw [← one_mul (f a c), ← hf_swap pab, mul_assoc]
  obtain rac | rca := total_of r a c
  · rw [hmul rba rac (hsymm pab) pac pbc]
  · rw [hmul rbc rca pbc (hsymm pac) (hsymm pab), mul_assoc, hf_swap (hsymm pac), mul_one]
#align multiplicative_of_symmetric_of_is_total multiplicative_of_symmetric_of_isTotal
#align additive_of_symmetric_of_is_total additive_of_symmetric_of_isTotal
-/

#print multiplicative_of_isTotal /-
/-- If a binary function from a type equipped with a total relation `r` to a monoid is
  anti-symmetric (i.e. satisfies `f a b * f b a = 1`), in order to show it is multiplicative
  (i.e. satisfies `f a c = f a b * f b c`), we may assume `r a b` and `r b c` are satisfied.
  We allow restricting to a subset specified by a predicate `p`. -/
@[to_additive additive_of_isTotal
      "If a binary function from a type equipped with a total relation\n  `r` to an additive monoid is anti-symmetric (i.e. satisfies `f a b + f b a = 0`), in order to show\n  it is additive (i.e. satisfies `f a c = f a b + f b c`), we may assume `r a b` and `r b c`\n  are satisfied. We allow restricting to a subset specified by a predicate `p`."]
theorem multiplicative_of_isTotal (p : α → Prop) (hswap : ∀ {a b}, p a → p b → f a b * f b a = 1)
    (hmul : ∀ {a b c}, r a b → r b c → p a → p b → p c → f a c = f a b * f b c) {a b c : α}
    (pa : p a) (pb : p b) (pc : p c) : f a c = f a b * f b c :=
  by
  apply multiplicative_of_symmetric_of_isTotal (fun a b => p a ∧ p b) r f fun _ _ => And.symm
  · simp_rw [and_imp]; exact @hswap
  · exact fun a b c rab rbc pab pbc pac => hmul rab rbc pab.1 pab.2 pac.2
  exacts [⟨pa, pb⟩, ⟨pb, pc⟩, ⟨pa, pc⟩]
#align multiplicative_of_is_total multiplicative_of_isTotal
#align additive_of_is_total additive_of_isTotal
-/

end Multiplicative

