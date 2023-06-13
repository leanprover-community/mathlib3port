/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module algebra.order.positive.ring
! leanprover-community/mathlib commit 448144f7ae193a8990cb7473c9e9a01990f64ac7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Ring.Defs
import Mathbin.Algebra.Ring.InjSurj

/-!
# Algebraic structures on the set of positive numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define various instances (`add_semigroup`, `ordered_comm_monoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/


open Function

namespace Positive

variable {M R K : Type _}

section AddBasic

variable [AddMonoid M] [Preorder M] [CovariantClass M M (· + ·) (· < ·)]

instance : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

#print Positive.coe_add /-
@[simp, norm_cast]
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl
#align positive.coe_add Positive.coe_add
-/

instance : AddSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddSemigroup _ coe_add

instance {M : Type _} [AddCommMonoid M] [Preorder M] [CovariantClass M M (· + ·) (· < ·)] :
    AddCommSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddCommSemigroup _ coe_add

instance {M : Type _} [AddLeftCancelMonoid M] [Preorder M] [CovariantClass M M (· + ·) (· < ·)] :
    AddLeftCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddLeftCancelSemigroup _ coe_add

instance {M : Type _} [AddRightCancelMonoid M] [Preorder M] [CovariantClass M M (· + ·) (· < ·)] :
    AddRightCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddRightCancelSemigroup _ coe_add

#print Positive.covariantClass_add_lt /-
instance covariantClass_add_lt :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun x y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_left hyz _⟩
#align positive.covariant_class_add_lt Positive.covariantClass_add_lt
-/

#print Positive.covariantClass_swap_add_lt /-
instance covariantClass_swap_add_lt [CovariantClass M M (swap (· + ·)) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun x y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_right hyz _⟩
#align positive.covariant_class_swap_add_lt Positive.covariantClass_swap_add_lt
-/

#print Positive.contravariantClass_add_lt /-
instance contravariantClass_add_lt [ContravariantClass M M (· + ·) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun x y z h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_left h⟩
#align positive.contravariant_class_add_lt Positive.contravariantClass_add_lt
-/

#print Positive.contravariantClass_swap_add_lt /-
instance contravariantClass_swap_add_lt [ContravariantClass M M (swap (· + ·)) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun x y z h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_right h⟩
#align positive.contravariant_class_swap_add_lt Positive.contravariantClass_swap_add_lt
-/

#print Positive.contravariantClass_add_le /-
instance contravariantClass_add_le [ContravariantClass M M (· + ·) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => Subtype.coe_le_coe.1 <| le_of_add_le_add_left h⟩
#align positive.contravariant_class_add_le Positive.contravariantClass_add_le
-/

#print Positive.contravariantClass_swap_add_le /-
instance contravariantClass_swap_add_le [ContravariantClass M M (swap (· + ·)) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· ≤ ·) :=
  ⟨fun x y z h => Subtype.coe_le_coe.1 <| le_of_add_le_add_right h⟩
#align positive.contravariant_class_swap_add_le Positive.contravariantClass_swap_add_le
-/

end AddBasic

#print Positive.covariantClass_add_le /-
instance covariantClass_add_le [AddMonoid M] [PartialOrder M] [CovariantClass M M (· + ·) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨fun x => StrictMono.monotone fun _ _ h => add_lt_add_left h _⟩
#align positive.covariant_class_add_le Positive.covariantClass_add_le
-/

section Mul

variable [StrictOrderedSemiring R]

instance : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

#print Positive.val_mul /-
@[simp]
theorem val_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl
#align positive.coe_mul Positive.val_mul
-/

instance : Pow { x : R // 0 < x } ℕ :=
  ⟨fun x n => ⟨x ^ n, pow_pos x.2 n⟩⟩

#print Positive.val_pow /-
@[simp]
theorem val_pow (x : { x : R // 0 < x }) (n : ℕ) : ↑(x ^ n) = (x ^ n : R) :=
  rfl
#align positive.coe_pow Positive.val_pow
-/

instance : Semigroup { x : R // 0 < x } :=
  Subtype.coe_injective.Semigroup coe val_mul

instance : Distrib { x : R // 0 < x } :=
  Subtype.coe_injective.Distrib _ coe_add val_mul

instance [Nontrivial R] : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

#print Positive.val_one /-
@[simp]
theorem val_one [Nontrivial R] : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl
#align positive.coe_one Positive.val_one
-/

instance [Nontrivial R] : Monoid { x : R // 0 < x } :=
  Subtype.coe_injective.Monoid _ val_one val_mul val_pow

end Mul

section mul_comm

instance [StrictOrderedCommSemiring R] [Nontrivial R] : OrderedCommMonoid { x : R // 0 < x } :=
  { Subtype.partialOrder _,
    Subtype.coe_injective.CommMonoid (coe : { x : R // 0 < x } → R) val_one val_mul val_pow with
    mul_le_mul_left := fun x y hxy c =>
      Subtype.coe_le_coe.1 <| mul_le_mul_of_nonneg_left hxy c.2.le }

/-- If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < x}` is a linear
ordered cancellative commutative monoid. -/
instance [LinearOrderedCommSemiring R] : LinearOrderedCancelCommMonoid { x : R // 0 < x } :=
  { Subtype.linearOrder _, Positive.orderedCommMonoid with
    le_of_mul_le_mul_left := fun a b c h => Subtype.coe_le_coe.1 <| (mul_le_mul_left a.2).1 h }

end mul_comm

end Positive

