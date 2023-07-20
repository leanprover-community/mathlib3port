/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.WithZero
import Mathbin.Algebra.Order.Monoid.WithTop
import Mathbin.Algebra.Order.Monoid.TypeTags

#align_import algebra.order.monoid.to_mul_bot from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative.
-/


universe u

variable {α : Type u}

namespace WithZero

attribute [local semireducible] WithZero

variable [Add α]

#print WithZero.toMulBot /-
/-- Making an additive monoid multiplicative then adding a zero is the same as adding a bottom
element then making it multiplicative. -/
def toMulBot : WithZero (Multiplicative α) ≃* Multiplicative (WithBot α) :=
  MulEquiv.refl _
#align with_zero.to_mul_bot WithZero.toMulBot
-/

#print WithZero.toMulBot_zero /-
@[simp]
theorem toMulBot_zero : toMulBot (0 : WithZero (Multiplicative α)) = Multiplicative.ofAdd ⊥ :=
  rfl
#align with_zero.to_mul_bot_zero WithZero.toMulBot_zero
-/

#print WithZero.toMulBot_coe /-
@[simp]
theorem toMulBot_coe (x : Multiplicative α) :
    toMulBot ↑x = Multiplicative.ofAdd (x.toAdd : WithBot α) :=
  rfl
#align with_zero.to_mul_bot_coe WithZero.toMulBot_coe
-/

#print WithZero.toMulBot_symm_bot /-
@[simp]
theorem toMulBot_symm_bot : toMulBot.symm (Multiplicative.ofAdd (⊥ : WithBot α)) = 0 :=
  rfl
#align with_zero.to_mul_bot_symm_bot WithZero.toMulBot_symm_bot
-/

#print WithZero.toMulBot_coe_ofAdd /-
@[simp]
theorem toMulBot_coe_ofAdd (x : α) :
    toMulBot.symm (Multiplicative.ofAdd (x : WithBot α)) = Multiplicative.ofAdd x :=
  rfl
#align with_zero.to_mul_bot_coe_of_add WithZero.toMulBot_coe_ofAdd
-/

variable [Preorder α] (a b : WithZero (Multiplicative α))

#print WithZero.toMulBot_strictMono /-
theorem toMulBot_strictMono : StrictMono (@toMulBot α _) := fun x y => id
#align with_zero.to_mul_bot_strict_mono WithZero.toMulBot_strictMono
-/

#print WithZero.toMulBot_le /-
@[simp]
theorem toMulBot_le : toMulBot a ≤ toMulBot b ↔ a ≤ b :=
  Iff.rfl
#align with_zero.to_mul_bot_le WithZero.toMulBot_le
-/

#print WithZero.toMulBot_lt /-
@[simp]
theorem toMulBot_lt : toMulBot a < toMulBot b ↔ a < b :=
  Iff.rfl
#align with_zero.to_mul_bot_lt WithZero.toMulBot_lt
-/

end WithZero

