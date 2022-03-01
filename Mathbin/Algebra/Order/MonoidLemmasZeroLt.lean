/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathbin.Algebra.CovariantAndContravariant

/-!
# Multiplication by ·positive· elements is monotonic

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

*  the notation `α>0` to stands for `{x : α // 0 < x}`.

If the type `α` also has a multiplication, then we combine this with (`contravariant_`)
`covariant_class`es to assume that multiplication by positive elements is (strictly) monotone on a
`mul_zero_class`, `monoid_with_zero`,...
More specifically, we use extensively the following typeclasses:

* monotone left
* * `covariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono α`,
    expressing that multiplication by positive elements on the left is monotone;
* * `covariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_strict_mono α`,
    expressing that multiplication by positive elements on the left is strictly monotone;
* monotone right
* * `covariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono α`,
    expressing that multiplication by positive elements on the right is monotone;
* * `covariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_strict_mono α`,
    expressing that multiplication by positive elements on the right is strictly monotone.
* reverse monotone left
* * `contravariant_class α>0 α (λ x y, x * y) (≤)`, abbreviated `pos_mul_mono_rev α`,
    expressing that multiplication by positive elements on the left is reverse monotone;
* * `contravariant_class α>0 α (λ x y, x * y) (<)`, abbreviated `pos_mul_reflect_lt α`,
    expressing that multiplication by positive elements on the left is strictly reverse monotone;
* reverse reverse monotone right
* * `contravariant_class α>0 α (λ x y, y * x) (≤)`, abbreviated `mul_pos_mono_rev α`,
    expressing that multiplication by positive elements on the right is reverse monotone;
* * `contravariant_class α>0 α (λ x y, y * x) (<)`, abbreviated `mul_pos_reflect_lt α`,
    expressing that multiplication by positive elements on the right is strictly reverse monotone.

##  Formalization comments

We use `α>0 = {x : α // 0 < x}` with a strict inequality since in most cases what happens with `0`
is clear.  This creates a few bumps in the first couple of proofs, where we have to split cases on
whether an element is `0` or not, but goes smoothly after that.  A further advantage is that we
only introduce notation for the positive elements and we do not need also the non-negative ones.
-/


/- I am changing the file `algebra/order/monoid_lemmas` incrementally, with the idea of
reproducing almost all of the proofs in `algebra/order/ring` with weaker assumptions. -/
universe u

variable {α : Type u}

-- mathport name: «exprα>0»
/-  Notation for positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation "α>0" => { x : α // 0 < x }

namespace ZeroLt

section AbbreviationsStrictMono

variable (X : Type u) [Mul X] [Zero X] [LT X]

/-- `zero_lt.pos_mul_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => x * y) (· < ·)

/-- `zero_lt.mul_pos_strict_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => y * x) (· < ·)

/-- `zero_lt.pos_mul_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly reverse monotone. -/
abbrev PosMulReflectLt : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => x * y) (· < ·)

/-- `zero_lt.mul_pos_reflect_lt α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly reverse monotone. -/
abbrev MulPosReflectLt : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => y * x) (· < ·)

end AbbreviationsStrictMono

section AbbreviationsMono

variable (X : Type _) [Mul X] [Zero X] [Preorderₓ X]

/-- `zero_lt.pos_mul_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is monotone. -/
abbrev PosMulMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => x * y) (· ≤ ·)

/-- `zero_lt.mul_pos_mono α` is an abbreviation for
`covariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is monotone. -/
abbrev MulPosMono : Prop :=
  CovariantClass { x : X // 0 < x } X (fun x y => y * x) (· ≤ ·)

/-- `zero_lt.pos_mul_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbrev PosMulMonoRev : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => x * y) (· ≤ ·)

/-- `zero_lt.mul_pos_mono_rev α` is an abbreviation for
`contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbrev MulPosMonoRev : Prop :=
  ContravariantClass { x : X // 0 < x } X (fun x y => y * x) (· ≤ ·)

end AbbreviationsMono

section HasMulZeroLt

variable [Mul α] [Zero α] [LT α]

theorem mul_lt_mul_left' [PosMulStrictMono α] {a b c : α} (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

theorem mul_lt_mul_right' [MulPosStrictMono α] {a b c : α} (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_left''`
theorem lt_of_mul_lt_mul_left' [PosMulReflectLt α] {a b c : α} (bc : a * b < a * c) (a0 : 0 < a) : b < c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc

-- proven with `a0 : 0 ≤ a` as `lt_of_mul_lt_mul_right''`
theorem lt_of_mul_lt_mul_right' [MulPosReflectLt α] {a b c : α} (bc : b * a < c * a) (a0 : 0 < a) : b < c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc

@[simp]
theorem mul_lt_mul_iff_left [PosMulStrictMono α] [PosMulReflectLt α] {a b c : α} (a0 : 0 < a) : a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _

@[simp]
theorem mul_lt_mul_iff_right [MulPosStrictMono α] [MulPosReflectLt α] {a b c : α} (a0 : 0 < a) :
    b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _

end HasMulZeroLt

end ZeroLt

