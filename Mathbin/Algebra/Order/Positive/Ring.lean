/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Algebra.Order.Ring

/-!
# Algebraic structures on the set of positive numbers

In this file we define various instances (`add_semigroup`, `ordered_comm_monoid` etc) on the
type `{x : R // 0 < x}`. In each case we try to require the weakest possible typeclass
assumptions on `R` but possibly, there is a room for improvements.
-/


open Function

namespace Positive

variable {M R K : Type _}

section AddBasic

variable [AddMonoidₓ M] [Preorderₓ M] [CovariantClass M M (· + ·) (· < ·)]

instance : Add { x : M // 0 < x } :=
  ⟨fun x y => ⟨x + y, add_pos x.2 y.2⟩⟩

@[simp, norm_cast]
theorem coe_add (x y : { x : M // 0 < x }) : ↑(x + y) = (x + y : M) :=
  rfl

instance : AddSemigroupₓ { x : M // 0 < x } :=
  Subtype.coe_injective.AddSemigroup _ coe_add

instance {M : Type _} [AddCommMonoidₓ M] [Preorderₓ M] [CovariantClass M M (· + ·) (· < ·)] :
    AddCommSemigroupₓ { x : M // 0 < x } :=
  Subtype.coe_injective.AddCommSemigroup _ coe_add

instance {M : Type _} [AddLeftCancelMonoid M] [Preorderₓ M] [CovariantClass M M (· + ·) (· < ·)] :
    AddLeftCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddLeftCancelSemigroup _ coe_add

instance {M : Type _} [AddRightCancelMonoid M] [Preorderₓ M] [CovariantClass M M (· + ·) (· < ·)] :
    AddRightCancelSemigroup { x : M // 0 < x } :=
  Subtype.coe_injective.AddRightCancelSemigroup _ coe_add

instance covariant_class_add_lt : CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun x y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_left hyz _⟩

instance covariant_class_swap_add_lt [CovariantClass M M (swap (· + ·)) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun x y z hyz => Subtype.coe_lt_coe.1 <| add_lt_add_right hyz _⟩

instance contravariant_class_add_lt [ContravariantClass M M (· + ·) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· < ·) :=
  ⟨fun x y z h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_left h⟩

instance contravariant_class_swap_add_lt [ContravariantClass M M (swap (· + ·)) (· < ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· < ·) :=
  ⟨fun x y z h => Subtype.coe_lt_coe.1 <| lt_of_add_lt_add_right h⟩

instance contravariant_class_add_le [ContravariantClass M M (· + ·) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨fun x y z h => Subtype.coe_le_coe.1 <| le_of_add_le_add_left h⟩

instance contravariant_class_swap_add_le [ContravariantClass M M (swap (· + ·)) (· ≤ ·)] :
    ContravariantClass { x : M // 0 < x } { x : M // 0 < x } (swap (· + ·)) (· ≤ ·) :=
  ⟨fun x y z h => Subtype.coe_le_coe.1 <| le_of_add_le_add_right h⟩

end AddBasic

instance covariant_class_add_le [AddMonoidₓ M] [PartialOrderₓ M] [CovariantClass M M (· + ·) (· < ·)] :
    CovariantClass { x : M // 0 < x } { x : M // 0 < x } (· + ·) (· ≤ ·) :=
  ⟨fun x => StrictMono.monotone fun _ _ h => add_lt_add_left h _⟩

section Mul

variable [OrderedSemiring R]

instance : Mul { x : R // 0 < x } :=
  ⟨fun x y => ⟨x * y, mul_pos x.2 y.2⟩⟩

@[simp]
theorem coe_mul (x y : { x : R // 0 < x }) : ↑(x * y) = (x * y : R) :=
  rfl

instance : Pow { x : R // 0 < x } ℕ :=
  ⟨fun x n => ⟨x ^ n, pow_pos x.2 n⟩⟩

@[simp]
theorem coe_pow (x : { x : R // 0 < x }) (n : ℕ) : ↑(x ^ n) = (x ^ n : R) :=
  rfl

instance : Semigroupₓ { x : R // 0 < x } :=
  Subtype.coe_injective.Semigroup coe coe_mul

instance : Distribₓ { x : R // 0 < x } :=
  Subtype.coe_injective.Distrib _ coe_add coe_mul

instance [Nontrivial R] : One { x : R // 0 < x } :=
  ⟨⟨1, one_pos⟩⟩

@[simp]
theorem coe_one [Nontrivial R] : ((1 : { x : R // 0 < x }) : R) = 1 :=
  rfl

instance [Nontrivial R] : Monoidₓ { x : R // 0 < x } :=
  Subtype.coe_injective.Monoid _ coe_one coe_mul coe_pow

end Mul

section mul_comm

instance [OrderedCommSemiring R] [Nontrivial R] : OrderedCommMonoid { x : R // 0 < x } :=
  { Subtype.partialOrder _, Subtype.coe_injective.CommMonoid (coe : { x : R // 0 < x } → R) coe_one coe_mul coe_pow with
    mul_le_mul_left := fun x y hxy c => Subtype.coe_le_coe.1 <| mul_le_mul_of_nonneg_left hxy c.2.le }

/-- If `R` is a nontrivial linear ordered commutative semiring, then `{x : R // 0 < x}` is a linear
ordered cancellative commutative monoid. We don't have a typeclass for linear ordered commutative
semirings, so we assume `[linear_ordered_semiring R] [is_commutative R (*)] instead. -/
instance [LinearOrderedSemiring R] [IsCommutative R (· * ·)] [Nontrivial R] :
    LinearOrderedCancelCommMonoid { x : R // 0 < x } :=
  { Subtype.linearOrder _,
    @Positive.Subtype.orderedCommMonoid R { ‹LinearOrderedSemiring R› with mul_comm := IsCommutative.comm } _ with
    le_of_mul_le_mul_left := fun a b c h => Subtype.coe_le_coe.1 <| (mul_le_mul_left a.2).1 h }

end mul_comm

end Positive

