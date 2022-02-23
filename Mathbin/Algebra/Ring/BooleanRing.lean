/-
Copyright (c) 2021 Bryan Gin-ge Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Gin-ge Chen
-/
import Mathbin.Tactic.Ring
import Mathbin.Tactic.Abel

/-!
# Boolean rings

A Boolean ring is a ring where multiplication is idempotent. They are equivalent to Boolean
algebras.

## Main declarations

* `boolean_ring`: a typeclass for rings where multiplication is idempotent.
* `boolean_ring.to_boolean_algebra`: every Boolean ring is a Boolean algebra; this definition and
  the `sup` and `inf` notations for `boolean_ring` are localized as instances in the
  `boolean_algebra_of_boolean_ring` locale.

## Tags

boolean ring, boolean algebra

-/


/-- A Boolean ring is a ring where multiplication is idempotent. -/
class BooleanRing (α) extends Ringₓ α where
  mul_self : ∀ a : α, a * a = a

section BooleanRing

variable {α : Type _} [BooleanRing α] (a b : α)

instance : IsIdempotent α (· * ·) :=
  ⟨BooleanRing.mul_self⟩

@[simp]
theorem mul_self : a * a = a :=
  BooleanRing.mul_self _

@[simp]
theorem add_self : a + a = 0 := by
  have : a + a = a + a + (a + a) :=
    calc
      a + a = (a + a) * (a + a) := by
        rw [mul_self]
      _ = a * a + a * a + (a * a + a * a) := by
        rw [add_mulₓ, mul_addₓ]
      _ = a + a + (a + a) := by
        rw [mul_self]
      
  rwa [self_eq_add_left] at this

@[simp]
theorem neg_eq : -a = a :=
  calc
    -a = -a + 0 := by
      rw [add_zeroₓ]
    _ = -a + -a + a := by
      rw [← neg_add_selfₓ, add_assocₓ]
    _ = a := by
      rw [add_self, zero_addₓ]
    

theorem add_eq_zero : a + b = 0 ↔ a = b :=
  calc
    a + b = 0 ↔ a = -b := add_eq_zero_iff_eq_neg
    _ ↔ a = b := by
      rw [neg_eq]
    

@[simp]
theorem mul_add_mul : a * b + b * a = 0 := by
  have : a + b = a + b + (a * b + b * a) :=
    calc
      a + b = (a + b) * (a + b) := by
        rw [mul_self]
      _ = a * a + a * b + (b * a + b * b) := by
        rw [add_mulₓ, mul_addₓ, mul_addₓ]
      _ = a + a * b + (b * a + b) := by
        simp only [mul_self]
      _ = a + b + (a * b + b * a) := by
        abel
      
  rwa [self_eq_add_rightₓ] at this

@[simp]
theorem sub_eq_add : a - b = a + b := by
  rw [sub_eq_add_neg, add_right_injₓ, neg_eq]

@[simp]
theorem mul_one_add_self : a * (1 + a) = 0 := by
  rw [mul_addₓ, mul_oneₓ, mul_self, add_self]

end BooleanRing

namespace BooleanRing

variable {α : Type _} [BooleanRing α]

-- Note [lower instance priority]
instance (priority := 100) : CommRingₓ α :=
  { (inferInstance : BooleanRing α) with
    mul_comm := fun a b => by
      rw [← add_eq_zero, mul_add_mul] }

/-- The join operation in a Boolean ring is `x + y + x*y`. -/
def hasSup : HasSup α :=
  ⟨fun x y => x + y + x * y⟩

/-- The meet operation in a Boolean ring is `x * y`. -/
def hasInf : HasInf α :=
  ⟨(· * ·)⟩

localized [-- Note [lower instance priority]
BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasSup

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasInf

theorem sup_comm (a b : α) : a⊔b = b⊔a := by
  dsimp only [(·⊔·)]
  ring

theorem inf_comm (a b : α) : a⊓b = b⊓a := by
  dsimp only [(·⊓·)]
  ring

theorem sup_assoc (a b c : α) : a⊔b⊔c = a⊔(b⊔c) := by
  dsimp only [(·⊔·)]
  ring

theorem inf_assoc (a b c : α) : a⊓b⊓c = a⊓(b⊓c) := by
  dsimp only [(·⊓·)]
  ring

theorem sup_inf_self (a b : α) : a⊔a⊓b = a := by
  dsimp only [(·⊔·), (·⊓·)]
  assoc_rw [mul_self, add_self, add_zeroₓ]

theorem inf_sup_self (a b : α) : a⊓(a⊔b) = a := by
  dsimp only [(·⊔·), (·⊓·)]
  assoc_rw [mul_addₓ, mul_addₓ, mul_self, mul_self, add_self, add_zeroₓ]

theorem le_sup_inf_aux (a b c : α) : (a + b + a * b) * (a + c + a * c) = a + b * c + a * (b * c) :=
  calc
    (a + b + a * b) * (a + c + a * c) =
        a * a + b * c + a * (b * c) + (a * b + a * a * b) + (a * c + a * a * c) + (a * b * c + a * a * b * c) :=
      by
      ring
    _ = a + b * c + a * (b * c) := by
      simp only [mul_self, add_self, add_zeroₓ]
    

theorem le_sup_inf (a b c : α) : (a⊔b)⊓(a⊔c)⊔(a⊔b⊓c) = a⊔b⊓c := by
  dsimp only [(·⊔·), (·⊓·)]
  rw [le_sup_inf_aux, add_self, mul_self, zero_addₓ]

/-- The "set difference" operation in a Boolean ring is `x * (1 + y)`. -/
def hasSdiff : HasSdiff α :=
  ⟨fun a b => a * (1 + b)⟩

/-- The bottom element of a Boolean ring is `0`. -/
def hasBot : HasBot α :=
  ⟨0⟩

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasSdiff

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.hasBot

theorem sup_inf_sdiff (a b : α) : a⊓b⊔a \ b = a :=
  calc
    a * b + a * (1 + b) + a * b * (a * (1 + b)) = a * b + a * (1 + b) + a * a * (b * (1 + b)) := by
      ac_rfl
    _ = a * b + (a + a * b) := by
      rw [mul_one_add_self, mul_zero, add_zeroₓ, mul_addₓ, mul_oneₓ]
    _ = a + (a * b + a * b) := by
      ac_rfl
    _ = a := by
      rw [add_self, add_zeroₓ]
    

theorem inf_inf_sdiff (a b : α) : a⊓b⊓a \ b = ⊥ :=
  calc
    a * b * (a * (1 + b)) = a * a * (b * (1 + b)) := by
      ac_rfl
    _ = 0 := by
      rw [mul_one_add_self, mul_zero]
    

/-- The Boolean algebra structure on a Boolean ring.

The data is defined so that:
* `a ⊔ b` unfolds to `a + b + a * b`
* `a ⊓ b` unfolds to `a * b`
* `a ≤ b` unfolds to `a + b + a * b = b`
* `⊥` unfolds to `0`
* `⊤` unfolds to `1`
* `aᶜ` unfolds to `1 + a`
* `a \ b` unfolds to `a * (1 + b)`
-/
def toBooleanAlgebra : BooleanAlgebra α :=
  { Lattice.mk' sup_comm sup_assoc inf_comm inf_assoc sup_inf_self inf_sup_self, hasSdiff, hasBot with
    le_sup_inf := le_sup_inf, top := 1,
    le_top := fun a =>
      show a + 1 + a * 1 = 1 by
        assoc_rw [mul_oneₓ, add_commₓ, add_self, add_zeroₓ],
    bot_le := fun a =>
      show 0 + a + 0 * a = a by
        rw [zero_mul, zero_addₓ, add_zeroₓ],
    Compl := fun a => 1 + a, sup_inf_sdiff := sup_inf_sdiff, inf_inf_sdiff := inf_inf_sdiff,
    inf_compl_le_bot := fun a =>
      show a * (1 + a) + 0 + a * (1 + a) * 0 = 0 by
        norm_num [mul_addₓ, mul_self, add_self],
    top_le_sup_compl := fun a => by
      change 1 + (a + (1 + a) + a * (1 + a)) + 1 * (a + (1 + a) + a * (1 + a)) = a + (1 + a) + a * (1 + a)
      norm_num [mul_addₓ, mul_self]
      rw [← add_assocₓ, add_self],
    sdiff_eq := fun a b => rfl }

localized [BooleanAlgebraOfBooleanRing] attribute [instance] BooleanRing.toBooleanAlgebra

end BooleanRing

