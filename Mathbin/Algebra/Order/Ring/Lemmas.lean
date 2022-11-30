/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Mathbin.Algebra.CovariantAndContravariant
import Mathbin.Algebra.GroupWithZero.Defs

/-!
# Multiplication by ·positive· elements is monotonic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/482
> Any changes to this file require a corresponding PR to mathlib4.

Let `α` be a type with `<` and `0`.  We use the type `{x : α // 0 < x}` of positive elements of `α`
to prove results about monotonicity of multiplication.  We also introduce the local notation `α>0`
for the subtype `{x : α // 0 < x}`:

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

## Notation

The following is local notation in this file:
* `α≥0`: `{x : α // 0 ≤ x}`
* `α>0`: `{x : α // 0 < x}`
-/


variable (α : Type _)

-- mathport name: «exprα≥0»
/- Notations for nonnegative and positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation "α≥0" => { x : α // 0 ≤ x }

-- mathport name: «exprα>0»
local notation "α>0" => { x : α // 0 < x }

section Abbreviations

variable [Mul α] [Zero α] [Preorder α]

#print PosMulMono /-
/-- `pos_mul_mono α` is an abbreviation for `covariant_class α≥0 α (λ x y, x * y) (≤)`,
expressing that multiplication by nonnegative elements on the left is monotone. -/
abbrev PosMulMono : Prop :=
  CovariantClass α≥0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono PosMulMono
-/

#print MulPosMono /-
/-- `mul_pos_mono α` is an abbreviation for `covariant_class α≥0 α (λ x y, y * x) (≤)`,
expressing that multiplication by nonnegative elements on the right is monotone. -/
abbrev MulPosMono : Prop :=
  CovariantClass α≥0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono MulPosMono
-/

#print PosMulStrictMono /-
/-- `pos_mul_strict_mono α` is an abbreviation for `covariant_class α>0 α (λ x y, x * y) (<)`,
expressing that multiplication by positive elements on the left is strictly monotone. -/
abbrev PosMulStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => x * y) (· < ·)
#align pos_mul_strict_mono PosMulStrictMono
-/

#print MulPosStrictMono /-
/-- `mul_pos_strict_mono α` is an abbreviation for `covariant_class α>0 α (λ x y, y * x) (<)`,
expressing that multiplication by positive elements on the right is strictly monotone. -/
abbrev MulPosStrictMono : Prop :=
  CovariantClass α>0 α (fun x y => y * x) (· < ·)
#align mul_pos_strict_mono MulPosStrictMono
-/

#print PosMulReflectLT /-
/-- `pos_mul_reflect_lt α` is an abbreviation for `contravariant_class α≥0 α (λ x y, x * y) (<)`,
expressing that multiplication by nonnegative elements on the left is strictly reverse monotone. -/
abbrev PosMulReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => x * y) (· < ·)
#align pos_mul_reflect_lt PosMulReflectLT
-/

#print MulPosReflectLT /-
/-- `mul_pos_reflect_lt α` is an abbreviation for `contravariant_class α≥0 α (λ x y, y * x) (<)`,
expressing that multiplication by nonnegative elements on the right is strictly reverse monotone. -/
abbrev MulPosReflectLT : Prop :=
  ContravariantClass α≥0 α (fun x y => y * x) (· < ·)
#align mul_pos_reflect_lt MulPosReflectLT
-/

#print PosMulMonoRev /-
/-- `pos_mul_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbrev PosMulMonoRev : Prop :=
  ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono_rev PosMulMonoRev
-/

#print MulPosMonoRev /-
/-- `mul_pos_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbrev MulPosMonoRev : Prop :=
  ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono_rev MulPosMonoRev
-/

end Abbreviations

variable {α} {a b c d : α}

section HasMulZero

variable [Mul α] [Zero α]

section Preorder

variable [Preorder α]

#print PosMulMono.toCovariantClassPosMulLE /-
instance PosMulMono.toCovariantClassPosMulLE [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨fun a b c bc => @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align pos_mul_mono.to_covariant_class_pos_mul_le PosMulMono.toCovariantClassPosMulLE
-/

#print MulPosMono.toCovariantClassPosMulLE /-
instance MulPosMono.toCovariantClassPosMulLE [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨fun a b c bc => @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align mul_pos_mono.to_covariant_class_pos_mul_le MulPosMono.toCovariantClassPosMulLE
-/

#print PosMulReflectLT.toContravariantClassPosMulLT /-
instance PosMulReflectLT.toContravariantClassPosMulLT [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a b c bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align
  pos_mul_reflect_lt.to_contravariant_class_pos_mul_lt PosMulReflectLT.toContravariantClassPosMulLT
-/

#print MulPosReflectLT.toContravariantClassPosMulLT /-
instance MulPosReflectLT.toContravariantClassPosMulLT [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a b c bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align
  mul_pos_reflect_lt.to_contravariant_class_pos_mul_lt MulPosReflectLT.toContravariantClassPosMulLT
-/

#print mul_le_mul_of_nonneg_left /-
theorem mul_le_mul_of_nonneg_left [PosMulMono α] (h : b ≤ c) (a0 : 0 ≤ a) : a * b ≤ a * c :=
  @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ h
#align mul_le_mul_of_nonneg_left mul_le_mul_of_nonneg_left
-/

#print mul_le_mul_of_nonneg_right /-
theorem mul_le_mul_of_nonneg_right [MulPosMono α] (h : b ≤ c) (a0 : 0 ≤ a) : b * a ≤ c * a :=
  @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ h
#align mul_le_mul_of_nonneg_right mul_le_mul_of_nonneg_right
-/

#print mul_lt_mul_of_pos_left /-
theorem mul_lt_mul_of_pos_left [PosMulStrictMono α] (bc : b < c) (a0 : 0 < a) : a * b < a * c :=
  @CovariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ bc
#align mul_lt_mul_of_pos_left mul_lt_mul_of_pos_left
-/

#print mul_lt_mul_of_pos_right /-
theorem mul_lt_mul_of_pos_right [MulPosStrictMono α] (bc : b < c) (a0 : 0 < a) : b * a < c * a :=
  @CovariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ bc
#align mul_lt_mul_of_pos_right mul_lt_mul_of_pos_right
-/

#print lt_of_mul_lt_mul_left /-
theorem lt_of_mul_lt_mul_left [PosMulReflectLT α] (h : a * b < a * c) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨a, a0⟩ _ _ h
#align lt_of_mul_lt_mul_left lt_of_mul_lt_mul_left
-/

#print lt_of_mul_lt_mul_right /-
theorem lt_of_mul_lt_mul_right [MulPosReflectLT α] (h : b * a < c * a) (a0 : 0 ≤ a) : b < c :=
  @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨a, a0⟩ _ _ h
#align lt_of_mul_lt_mul_right lt_of_mul_lt_mul_right
-/

#print le_of_mul_le_mul_left /-
theorem le_of_mul_le_mul_left [PosMulMonoRev α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_left le_of_mul_le_mul_left
-/

#print le_of_mul_le_mul_right /-
theorem le_of_mul_le_mul_right [MulPosMonoRev α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_right le_of_mul_le_mul_right
-/

alias lt_of_mul_lt_mul_left ← lt_of_mul_lt_mul_of_nonneg_left

alias lt_of_mul_lt_mul_right ← lt_of_mul_lt_mul_of_nonneg_right

alias le_of_mul_le_mul_left ← le_of_mul_le_mul_of_pos_left

alias le_of_mul_le_mul_right ← le_of_mul_le_mul_of_pos_right

#print mul_lt_mul_left /-
@[simp]
theorem mul_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a * c ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· < ·) _ _ ⟨a, a0⟩ _ _
#align mul_lt_mul_left mul_lt_mul_left
-/

#print mul_lt_mul_right /-
@[simp]
theorem mul_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    b * a < c * a ↔ b < c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· < ·) _ _ ⟨a, a0⟩ _ _
#align mul_lt_mul_right mul_lt_mul_right
-/

#print mul_le_mul_left /-
@[simp]
theorem mul_le_mul_left [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_left mul_le_mul_left
-/

#print mul_le_mul_right /-
@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => y * x) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_right mul_le_mul_right
-/

#print mul_lt_mul_of_pos_of_nonneg /-
theorem mul_lt_mul_of_pos_of_nonneg [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 ≤ d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans_le (mul_le_mul_of_nonneg_right h₁ d0)
#align mul_lt_mul_of_pos_of_nonneg mul_lt_mul_of_pos_of_nonneg
-/

#print mul_lt_mul_of_le_of_le' /-
theorem mul_lt_mul_of_le_of_le' [PosMulStrictMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 ≤ c) : a * c < b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans_lt (mul_lt_mul_of_pos_left h₂ b0)
#align mul_lt_mul_of_le_of_le' mul_lt_mul_of_le_of_le'
-/

#print mul_lt_mul_of_nonneg_of_pos /-
theorem mul_lt_mul_of_nonneg_of_pos [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (a0 : 0 ≤ a) (d0 : 0 < d) : a * c < b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans_lt (mul_lt_mul_of_pos_right h₁ d0)
#align mul_lt_mul_of_nonneg_of_pos mul_lt_mul_of_nonneg_of_pos
-/

#print mul_lt_mul_of_le_of_lt' /-
theorem mul_lt_mul_of_le_of_lt' [PosMulMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c ≤ d)
    (b0 : 0 ≤ b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans_le (mul_le_mul_of_nonneg_left h₂ b0)
#align mul_lt_mul_of_le_of_lt' mul_lt_mul_of_le_of_lt'
-/

#print mul_lt_mul_of_pos_of_pos /-
theorem mul_lt_mul_of_pos_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (a0 : 0 < a) (d0 : 0 < d) : a * c < b * d :=
  (mul_lt_mul_of_pos_left h₂ a0).trans (mul_lt_mul_of_pos_right h₁ d0)
#align mul_lt_mul_of_pos_of_pos mul_lt_mul_of_pos_of_pos
-/

#print mul_lt_mul_of_lt_of_lt' /-
theorem mul_lt_mul_of_lt_of_lt' [PosMulStrictMono α] [MulPosStrictMono α] (h₁ : a < b) (h₂ : c < d)
    (b0 : 0 < b) (c0 : 0 < c) : a * c < b * d :=
  (mul_lt_mul_of_pos_right h₁ c0).trans (mul_lt_mul_of_pos_left h₂ b0)
#align mul_lt_mul_of_lt_of_lt' mul_lt_mul_of_lt_of_lt'
-/

#print mul_lt_of_mul_lt_of_nonneg_left /-
theorem mul_lt_of_mul_lt_of_nonneg_left [PosMulMono α] (h : a * b < c) (hdb : d ≤ b) (ha : 0 ≤ a) :
    a * d < c :=
  (mul_le_mul_of_nonneg_left hdb ha).trans_lt h
#align mul_lt_of_mul_lt_of_nonneg_left mul_lt_of_mul_lt_of_nonneg_left
-/

#print lt_mul_of_lt_mul_of_nonneg_left /-
theorem lt_mul_of_lt_mul_of_nonneg_left [PosMulMono α] (h : a < b * c) (hcd : c ≤ d) (hb : 0 ≤ b) :
    a < b * d :=
  h.trans_le <| mul_le_mul_of_nonneg_left hcd hb
#align lt_mul_of_lt_mul_of_nonneg_left lt_mul_of_lt_mul_of_nonneg_left
-/

#print mul_lt_of_mul_lt_of_nonneg_right /-
theorem mul_lt_of_mul_lt_of_nonneg_right [MulPosMono α] (h : a * b < c) (hda : d ≤ a) (hb : 0 ≤ b) :
    d * b < c :=
  (mul_le_mul_of_nonneg_right hda hb).trans_lt h
#align mul_lt_of_mul_lt_of_nonneg_right mul_lt_of_mul_lt_of_nonneg_right
-/

#print lt_mul_of_lt_mul_of_nonneg_right /-
theorem lt_mul_of_lt_mul_of_nonneg_right [MulPosMono α] (h : a < b * c) (hbd : b ≤ d) (hc : 0 ≤ c) :
    a < d * c :=
  h.trans_le <| mul_le_mul_of_nonneg_right hbd hc
#align lt_mul_of_lt_mul_of_nonneg_right lt_mul_of_lt_mul_of_nonneg_right
-/

end Preorder

section LinearOrder

variable [LinearOrder α]

-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.to_pos_mul_mono_rev [PosMulStrictMono α] :
    PosMulMonoRev α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_left h' x.Prop⟩
#align pos_mul_strict_mono.to_pos_mul_mono_rev PosMulStrictMono.to_pos_mul_mono_rev

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.to_mul_pos_mono_rev [MulPosStrictMono α] :
    MulPosMonoRev α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_right h' x.Prop⟩
#align mul_pos_strict_mono.to_mul_pos_mono_rev MulPosStrictMono.to_mul_pos_mono_rev

theorem PosMulMonoRev.to_pos_mul_strict_mono [PosMulMonoRev α] : PosMulStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_left h' x.Prop⟩
#align pos_mul_mono_rev.to_pos_mul_strict_mono PosMulMonoRev.to_pos_mul_strict_mono

theorem MulPosMonoRev.to_mul_pos_strict_mono [MulPosMonoRev α] : MulPosStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_right h' x.Prop⟩
#align mul_pos_mono_rev.to_mul_pos_strict_mono MulPosMonoRev.to_mul_pos_strict_mono

theorem pos_mul_strict_mono_iff_pos_mul_mono_rev : PosMulStrictMono α ↔ PosMulMonoRev α :=
  ⟨@PosMulStrictMono.to_pos_mul_mono_rev _ _ _ _, @PosMulMonoRev.to_pos_mul_strict_mono _ _ _ _⟩
#align pos_mul_strict_mono_iff_pos_mul_mono_rev pos_mul_strict_mono_iff_pos_mul_mono_rev

theorem mul_pos_strict_mono_iff_mul_pos_mono_rev : MulPosStrictMono α ↔ MulPosMonoRev α :=
  ⟨@MulPosStrictMono.to_mul_pos_mono_rev _ _ _ _, @MulPosMonoRev.to_mul_pos_strict_mono _ _ _ _⟩
#align mul_pos_strict_mono_iff_mul_pos_mono_rev mul_pos_strict_mono_iff_mul_pos_mono_rev

#print PosMulReflectLT.toPosMulMono /-
theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_left h' x.Prop⟩
#align pos_mul_reflect_lt.to_pos_mul_mono PosMulReflectLT.toPosMulMono
-/

#print MulPosReflectLT.toMulPosMono /-
theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_right h' x.Prop⟩
#align mul_pos_reflect_lt.to_mul_pos_mono MulPosReflectLT.toMulPosMono
-/

theorem PosMulMono.to_pos_mul_reflect_lt [PosMulMono α] : PosMulReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_left h' x.Prop⟩
#align pos_mul_mono.to_pos_mul_reflect_lt PosMulMono.to_pos_mul_reflect_lt

theorem MulPosMono.to_mul_pos_reflect_lt [MulPosMono α] : MulPosReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_right h' x.Prop⟩
#align mul_pos_mono.to_mul_pos_reflect_lt MulPosMono.to_mul_pos_reflect_lt

theorem pos_mul_mono_iff_pos_mul_reflect_lt : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.to_pos_mul_reflect_lt _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩
#align pos_mul_mono_iff_pos_mul_reflect_lt pos_mul_mono_iff_pos_mul_reflect_lt

theorem mul_pos_mono_iff_mul_pos_reflect_lt : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.to_mul_pos_reflect_lt _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩
#align mul_pos_mono_iff_mul_pos_reflect_lt mul_pos_mono_iff_mul_pos_reflect_lt

end LinearOrder

end HasMulZero

section MulZeroClass

variable [MulZeroClass α]

section Preorder

variable [Preorder α]

/- warning: left.mul_pos -> Left.mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3616 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3619 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3616], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3616) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3616) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3616) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3613)) a b))
Case conversion may be inaccurate. Consider using '#align left.mul_pos Left.mul_posₓ'. -/
/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha
#align left.mul_pos Left.mul_pos

alias Left.mul_pos ← mul_pos

/- warning: mul_neg_of_pos_of_neg -> mul_neg_of_pos_of_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3682 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3685 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3682], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3682) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3682) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3682) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3679))))
Case conversion may be inaccurate. Consider using '#align mul_neg_of_pos_of_neg mul_neg_of_pos_of_negₓ'. -/
theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [mul_zero] using mul_lt_mul_of_pos_left hb ha
#align mul_neg_of_pos_of_neg mul_neg_of_pos_of_neg

/- warning: zero_lt_mul_left -> zero_lt_mul_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} {c : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) c) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) c b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3749 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3752 : PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743))) c) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743)) c b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3746) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3743))) b))
Case conversion may be inaccurate. Consider using '#align zero_lt_mul_left zero_lt_mul_leftₓ'. -/
@[simp]
theorem zero_lt_mul_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < c) : 0 < c * b ↔ 0 < b :=
  by 
  convert mul_lt_mul_left h
  simp
#align zero_lt_mul_left zero_lt_mul_left

/- warning: right.mul_pos -> Right.mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3823 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3826 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3823], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3823) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3823) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3823) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3820)) a b))
Case conversion may be inaccurate. Consider using '#align right.mul_pos Right.mul_posₓ'. -/
/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
#align right.mul_pos Right.mul_pos

/- warning: mul_neg_of_neg_of_pos -> mul_neg_of_neg_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3888 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3891 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3888], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3888) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3888) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3888) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3885))))
Case conversion may be inaccurate. Consider using '#align mul_neg_of_neg_of_pos mul_neg_of_neg_of_posₓ'. -/
theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [zero_mul] using mul_lt_mul_of_pos_right ha hb
#align mul_neg_of_neg_of_pos mul_neg_of_neg_of_pos

/- warning: zero_lt_mul_right -> zero_lt_mul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {b : α} {c : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) c) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b c)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3955 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3958 : MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949))) c) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949)) b c)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3952) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.3949))) b))
Case conversion may be inaccurate. Consider using '#align zero_lt_mul_right zero_lt_mul_rightₓ'. -/
@[simp]
theorem zero_lt_mul_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < c) :
    0 < b * c ↔ 0 < b := by 
  convert mul_lt_mul_right h
  simp
#align zero_lt_mul_right zero_lt_mul_right

/- warning: left.mul_nonneg -> Left.mul_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4029 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4032 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4029], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4029) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4029) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4029) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4026)) a b))
Case conversion may be inaccurate. Consider using '#align left.mul_nonneg Left.mul_nonnegₓ'. -/
/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align left.mul_nonneg Left.mul_nonneg

alias Left.mul_nonneg ← mul_nonneg

/- warning: mul_nonpos_of_nonneg_of_nonpos -> mul_nonpos_of_nonneg_of_nonpos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4095 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4098 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4095], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4095) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4095) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4095) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4092))))
Case conversion may be inaccurate. Consider using '#align mul_nonpos_of_nonneg_of_nonpos mul_nonpos_of_nonneg_of_nonposₓ'. -/
theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align mul_nonpos_of_nonneg_of_nonpos mul_nonpos_of_nonneg_of_nonpos

/- warning: right.mul_nonneg -> Right.mul_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4162 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4165 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4162], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4162) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4162) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4162) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4159)) a b))
Case conversion may be inaccurate. Consider using '#align right.mul_nonneg Right.mul_nonnegₓ'. -/
/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align right.mul_nonneg Right.mul_nonneg

/- warning: mul_nonpos_of_nonpos_of_nonneg -> mul_nonpos_of_nonpos_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4227 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4230 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4227], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4227) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4227) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4227) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4224))))
Case conversion may be inaccurate. Consider using '#align mul_nonpos_of_nonpos_of_nonneg mul_nonpos_of_nonpos_of_nonnegₓ'. -/
theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align mul_nonpos_of_nonpos_of_nonneg mul_nonpos_of_nonpos_of_nonneg

/- warning: pos_of_mul_pos_right -> pos_of_mul_pos_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4291 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4294 : PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4291], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4291) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4291) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4291) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4288))) b)
Case conversion may be inaccurate. Consider using '#align pos_of_mul_pos_right pos_of_mul_pos_rightₓ'. -/
theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((mul_zero a).symm ▸ h : a * 0 < a * b) ha
#align pos_of_mul_pos_right pos_of_mul_pos_right

/- warning: pos_of_mul_pos_left -> pos_of_mul_pos_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4345 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4348 : MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4345], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4345) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4345) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4345) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4342))) a)
Case conversion may be inaccurate. Consider using '#align pos_of_mul_pos_left pos_of_mul_pos_leftₓ'. -/
theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((zero_mul b).symm ▸ h : 0 * b < a * b) hb
#align pos_of_mul_pos_left pos_of_mul_pos_left

/- warning: pos_iff_pos_of_mul_pos -> pos_iff_pos_of_mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4402 : PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4405 : MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396))) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4399) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4396))) b))
Case conversion may be inaccurate. Consider using '#align pos_iff_pos_of_mul_pos pos_iff_pos_of_mul_posₓ'. -/
theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩
#align pos_iff_pos_of_mul_pos pos_iff_pos_of_mul_pos

/- warning: mul_le_mul_of_le_of_le -> mul_le_mul_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b d))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4454 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4457 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448))) d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4451) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4448)) b d))
Case conversion may be inaccurate. Consider using '#align mul_le_mul_of_le_of_le mul_le_mul_of_le_of_leₓ'. -/
theorem mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a)
    (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans <| mul_le_mul_of_nonneg_right h₁ d0
#align mul_le_mul_of_le_of_le mul_le_mul_of_le_of_le

/- warning: mul_le_mul -> mul_le_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b d))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4512 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4515 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4509) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4506)) b d))
Case conversion may be inaccurate. Consider using '#align mul_le_mul mul_le_mulₓ'. -/
theorem mul_le_mul [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c)
    (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans <| mul_le_mul_of_nonneg_left h₂ b0
#align mul_le_mul mul_le_mul

/- warning: mul_self_le_mul_self -> mul_self_le_mul_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a a) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4570 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4573 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4567) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564)) a a) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4564)) b b))
Case conversion may be inaccurate. Consider using '#align mul_self_le_mul_self mul_self_le_mul_selfₓ'. -/
theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab
#align mul_self_le_mul_self mul_self_le_mul_self

/- warning: mul_le_of_mul_le_of_nonneg_left -> mul_le_of_mul_le_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) d b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a d) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4615 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612) d b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4612) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4609)) a d) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_mul_le_of_nonneg_left mul_le_of_mul_le_of_nonneg_leftₓ'. -/
theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h
#align mul_le_of_mul_le_of_nonneg_left mul_le_of_mul_le_of_nonneg_left

/- warning: le_mul_of_le_mul_of_nonneg_left -> le_mul_of_le_mul_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b d))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4661 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658) c d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4658) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4655)) b d))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_mul_of_nonneg_left le_mul_of_le_mul_of_nonneg_leftₓ'. -/
theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)
#align le_mul_of_le_mul_of_nonneg_left le_mul_of_le_mul_of_nonneg_left

/- warning: mul_le_of_mul_le_of_nonneg_right -> mul_le_of_mul_le_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) d a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) d b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4706 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703) d a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4703) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4700)) d b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_mul_le_of_nonneg_right mul_le_of_mul_le_of_nonneg_rightₓ'. -/
theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h
#align mul_le_of_mul_le_of_nonneg_right mul_le_of_mul_le_of_nonneg_right

/- warning: le_mul_of_le_mul_of_nonneg_right -> le_mul_of_le_mul_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : Preorder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) _inst_2], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) b d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_2) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) d c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4752 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749) b d) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4749) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4746)) d c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_mul_of_nonneg_right le_mul_of_le_mul_of_nonneg_rightₓ'. -/
theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)
#align le_mul_of_le_mul_of_nonneg_right le_mul_of_le_mul_of_nonneg_right

end Preorder

section PartialOrder

variable [PartialOrder α]

/- warning: pos_mul_mono_iff_covariant_pos -> posMulMono_iff_covariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x) y) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806)) (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4806))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4819) x) y) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4848 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4850 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4809)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4848 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4850))
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_posₓ'. -/
theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨@PosMulMono.toCovariantClassPosMulLE _ _ _ _, fun h =>
    ⟨fun a b c h => by 
      obtain ha | ha := a.prop.eq_or_gt
      · simp only [ha, zero_mul]
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_pos

/- warning: mul_pos_mono_iff_covariant_pos -> mulPosMono_iff_covariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) y ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944)) y (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4944))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4957) x)) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4986 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4988 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4947)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4986 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4988))
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_posₓ'. -/
theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.toCovariantClassPosMulLE _ _ _ _, fun h =>
    ⟨fun a b c h => by 
      obtain ha | ha := a.prop.eq_or_gt
      · simp only [ha, mul_zero]
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_pos

/- warning: pos_mul_reflect_lt_iff_contravariant_pos -> posMulReflectLT_iff_contravariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x) y) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085 : PartialOrder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082)) (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5082))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5095) x) y) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5124 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5126 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5085)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5124 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5126))
Case conversion may be inaccurate. Consider using '#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_posₓ'. -/
theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.toContravariantClassPosMulLT _ _ _ _, fun h =>
    ⟨fun a b c h => by 
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_pos

/- warning: mul_pos_reflect_lt_iff_contravariant_pos -> mulPosReflectLT_iff_contravariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) y ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223 : PartialOrder.{u_1} α], Iff (MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220)) y (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5220))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5233) x)) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5262 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5264 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5223)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5262 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5264))
Case conversion may be inaccurate. Consider using '#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_posₓ'. -/
theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.toContravariantClassPosMulLT _ _ _ _, fun h =>
    ⟨fun a b c h => by 
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_pos

/- warning: pos_mul_strict_mono.to_pos_mul_mono -> PosMulStrictMono.toPosMulMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5361 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5364 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5367 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5361) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5361) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5364)], PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5361) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5361) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5364)
Case conversion may be inaccurate. Consider using '#align pos_mul_strict_mono.to_pos_mul_mono PosMulStrictMono.toPosMulMonoₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 <|
    ⟨fun a => StrictMono.monotone <| @CovariantClass.elim _ _ _ _ _ _⟩
#align pos_mul_strict_mono.to_pos_mul_mono PosMulStrictMono.toPosMulMono

/- warning: mul_pos_strict_mono.to_mul_pos_mono -> MulPosStrictMono.toMulPosMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5410 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5413 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5416 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5410) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5410) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5413)], MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5410) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5410) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5413)
Case conversion may be inaccurate. Consider using '#align mul_pos_strict_mono.to_mul_pos_mono MulPosStrictMono.toMulPosMonoₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 <|
    ⟨fun a => StrictMono.monotone <| @CovariantClass.elim _ _ _ _ _ _⟩
#align mul_pos_strict_mono.to_mul_pos_mono MulPosStrictMono.toMulPosMono

/- warning: pos_mul_mono_rev.to_pos_mul_reflect_lt -> PosMulMonoRev.toPosMulReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5459 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5462 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5465 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5459) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5459) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5462)], PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5459) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5459) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5462)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_rev.to_pos_mul_reflect_lt PosMulMonoRev.toPosMulReflectLTₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) PosMulMonoRev.toPosMulReflectLT [PosMulMonoRev α] : PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by
        rintro rfl
        simpa using h⟩
#align pos_mul_mono_rev.to_pos_mul_reflect_lt PosMulMonoRev.toPosMulReflectLT

/- warning: mul_pos_mono_rev.to_mul_pos_reflect_lt -> MulPosMonoRev.toMulPosReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5504 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5507 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5510 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5504) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5504) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5507)], MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5504) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5504) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5507)
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_rev.to_mul_pos_reflect_lt MulPosMonoRev.toMulPosReflectLTₓ'. -/
-- see Note [lower instance priority]
instance (priority := 100) MulPosMonoRev.toMulPosReflectLT [MulPosMonoRev α] : MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by
        rintro rfl
        simpa using h⟩
#align mul_pos_mono_rev.to_mul_pos_reflect_lt MulPosMonoRev.toMulPosReflectLT

/- warning: mul_left_cancel_iff_of_pos -> mul_left_cancel_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a c)) (Eq.{succ u_1} α b c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5549 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5552 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5549)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5549)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546))) a) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5546)) a c)) (Eq.{succ u_1} α b c))
Case conversion may be inaccurate. Consider using '#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_posₓ'. -/
theorem mul_left_cancel_iff_of_pos [PosMulMonoRev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <| le_of_mul_le_mul_of_pos_left h.ge a0,
    congr_arg _⟩
#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_pos

/- warning: mul_right_cancel_iff_of_pos -> mul_right_cancel_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) c b)) (Eq.{succ u_1} α a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5604 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5607 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5604)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5604)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5601)) c b)) (Eq.{succ u_1} α a c))
Case conversion may be inaccurate. Consider using '#align mul_right_cancel_iff_of_pos mul_right_cancel_iff_of_posₓ'. -/
theorem mul_right_cancel_iff_of_pos [MulPosMonoRev α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h =>
    (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <| le_of_mul_le_mul_of_pos_right h.ge b0,
    congr_arg _⟩
#align mul_right_cancel_iff_of_pos mul_right_cancel_iff_of_pos

/- warning: mul_eq_mul_iff_eq_and_eq_of_pos -> mul_eq_mul_iff_eq_and_eq_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_4 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_5 : PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_6 : MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5673 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5676 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5679 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5682 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5670)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667))) d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5667)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_iff_eq_and_eq_of_pos mul_eq_mul_iff_eq_and_eq_of_posₓ'. -/
theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α]
    [MulPosMonoRev α] (hac : a ≤ b) (hbd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos a0).mp h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iff_of_pos d0).mp h, rfl⟩
  exact ((mul_lt_mul_of_pos_of_pos hac hbd a0 d0).Ne h).elim
#align mul_eq_mul_iff_eq_and_eq_of_pos mul_eq_mul_iff_eq_and_eq_of_pos

/- warning: mul_eq_mul_iff_eq_and_eq_of_pos' -> mul_eq_mul_iff_eq_and_eq_of_pos' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_4 : MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_5 : PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)] [_inst_6 : MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) c) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5819 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5822 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5825 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5828 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5816)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813))) c) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5813)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
Case conversion may be inaccurate. Consider using '#align mul_eq_mul_iff_eq_and_eq_of_pos' mul_eq_mul_iff_eq_and_eq_of_pos'ₓ'. -/
theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α] [PosMulMonoRev α]
    [MulPosMonoRev α] (hac : a ≤ b) (hbd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d := by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos b0).mp h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iff_of_pos c0).mp h, rfl⟩
  exact ((mul_lt_mul_of_lt_of_lt' hac hbd b0 c0).Ne h).elim
#align mul_eq_mul_iff_eq_and_eq_of_pos' mul_eq_mul_iff_eq_and_eq_of_pos'

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/- warning: pos_and_pos_or_neg_and_neg_of_mul_pos -> pos_and_pos_or_neg_and_neg_of_mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Or (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b)) (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5980 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5983 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974)) a b)) -> (Or (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974))) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974))) b)) (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5977))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5974))))))
Case conversion may be inaccurate. Consider using '#align pos_and_pos_or_neg_and_neg_of_mul_pos pos_and_pos_or_neg_and_neg_of_mul_posₓ'. -/
theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 := by
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
  · rw [zero_mul] at hab
    exact hab.false.elim
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
#align pos_and_pos_or_neg_and_neg_of_mul_pos pos_and_pos_or_neg_and_neg_of_mul_pos

/- warning: neg_of_mul_pos_right -> neg_of_mul_pos_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6115 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6118 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6112))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6109))))
Case conversion may be inaccurate. Consider using '#align neg_of_mul_pos_right neg_of_mul_pos_rightₓ'. -/
theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2
#align neg_of_mul_pos_right neg_of_mul_pos_right

/- warning: neg_of_mul_pos_left -> neg_of_mul_pos_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6163 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6166 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6160))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6157))))
Case conversion may be inaccurate. Consider using '#align neg_of_mul_pos_left neg_of_mul_pos_leftₓ'. -/
theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1
#align neg_of_mul_pos_left neg_of_mul_pos_left

/- warning: neg_iff_neg_of_mul_pos -> neg_iff_neg_of_mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6211 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6214 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6208))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6205)))))
Case conversion may be inaccurate. Consider using '#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_posₓ'. -/
theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩
#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_pos

/- warning: left.neg_of_mul_neg_left -> Left.neg_of_mul_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6263 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6266 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6263))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6263))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6263))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6263))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6260))))
Case conversion may be inaccurate. Consider using '#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_leftₓ'. -/
theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h
#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_left

/- warning: right.neg_of_mul_neg_left -> Right.neg_of_mul_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6316 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6319 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6316))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6316))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6316))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6316))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6313))))
Case conversion may be inaccurate. Consider using '#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_leftₓ'. -/
theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h
#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_left

/- warning: left.neg_of_mul_neg_right -> Left.neg_of_mul_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6369 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6372 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6369))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6369))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6369))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6369))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6366))))
Case conversion may be inaccurate. Consider using '#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_rightₓ'. -/
theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h
#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_right

/- warning: right.neg_of_mul_neg_right -> Right.neg_of_mul_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6422 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6425 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6422))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6422))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6422))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6422))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6419))))
Case conversion may be inaccurate. Consider using '#align right.neg_of_mul_neg_right Right.neg_of_mul_neg_rightₓ'. -/
theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Right.mul_nonneg h2 h1).not_lt h
#align right.neg_of_mul_neg_right Right.neg_of_mul_neg_right

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α]

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/


/- warning: le_mul_iff_one_le_right -> le_mul_iff_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulMonoRev.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6504 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6507 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6513 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6504) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6507 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6516 : PosMulMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6504) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6507 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6507)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6504)) a b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6510) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6504))) b))
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_right le_mul_iff_one_le_rightₓ'. -/
@[simp]
theorem le_mul_iff_one_le_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align le_mul_iff_one_le_right le_mul_iff_one_le_right

/- warning: lt_mul_iff_one_lt_right -> lt_mul_iff_one_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6580 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6583 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6589 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6580) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6583 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6592 : PosMulReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6580) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6583 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6583)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6580)) a b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6586) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6580))) b))
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_right lt_mul_iff_one_lt_rightₓ'. -/
@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align lt_mul_iff_one_lt_right lt_mul_iff_one_lt_right

/- warning: mul_le_iff_le_one_right -> mul_le_iff_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulMonoRev.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6656 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6659 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6665 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6656) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6659 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6668 : PosMulMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6656) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6659 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6659)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6656)) a b) a) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6662) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6656)))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_right mul_le_iff_le_one_rightₓ'. -/
@[simp]
theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align mul_le_iff_le_one_right mul_le_iff_le_one_right

/- warning: mul_lt_iff_lt_one_right -> mul_lt_iff_lt_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6732 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6735 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6741 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6732) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6735 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6744 : PosMulReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6732) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6735 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6735)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6732)) a b) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6738) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6732)))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_right mul_lt_iff_lt_one_rightₓ'. -/
@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align mul_lt_iff_lt_one_right mul_lt_iff_lt_one_right

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


/- warning: le_mul_iff_one_le_left -> le_mul_iff_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMonoRev.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6809 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6812 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6818 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6809) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6812 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6821 : MulPosMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6809) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6812 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6812)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6809)) b a)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6815) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6809))) b))
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_left le_mul_iff_one_le_leftₓ'. -/
@[simp]
theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)
#align le_mul_iff_one_le_left le_mul_iff_one_le_left

/- warning: lt_mul_iff_one_lt_left -> lt_mul_iff_one_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6885 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6888 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6894 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6885) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6888 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6897 : MulPosReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6885) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6888 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6888)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6885)) b a)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6891) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6885))) b))
Case conversion may be inaccurate. Consider using '#align lt_mul_iff_one_lt_left lt_mul_iff_one_lt_leftₓ'. -/
@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)
#align lt_mul_iff_one_lt_left lt_mul_iff_one_lt_left

/- warning: mul_le_iff_le_one_left -> mul_le_iff_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMonoRev.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6961 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6964 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6970 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6961) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6964 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6973 : MulPosMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6961) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6964 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6964)) b) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6961)) a b) b) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6967) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6961)))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_left mul_le_iff_le_one_leftₓ'. -/
@[simp]
theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosMonoRev α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)
#align mul_le_iff_le_one_left mul_le_iff_le_one_left

/- warning: mul_lt_iff_lt_one_left -> mul_lt_iff_lt_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7037 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7040 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7046 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7037) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7040 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7049 : MulPosReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7037) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7040 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7040)) b) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7037)) a b) b) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7043) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7037)))))
Case conversion may be inaccurate. Consider using '#align mul_lt_iff_lt_one_left mul_lt_iff_lt_one_leftₓ'. -/
@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)
#align mul_lt_iff_lt_one_left mul_lt_iff_lt_one_left

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`. -/


/- warning: mul_le_of_le_one_left -> mul_le_of_le_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7114 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7117 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7120 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7123 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7114) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7117 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7120], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7120) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7117)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7120) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7114)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7120) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7114)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_left mul_le_of_le_one_leftₓ'. -/
theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align mul_le_of_le_one_left mul_le_of_le_one_left

/- warning: le_mul_of_one_le_left -> le_mul_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7181 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7184 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7187 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7190 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7181) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7184 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7187], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7187) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7184)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7187) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7181))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7187) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7181)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_left le_mul_of_one_le_leftₓ'. -/
theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align le_mul_of_one_le_left le_mul_of_one_le_left

/- warning: mul_le_of_le_one_right -> mul_le_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7248 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7251 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7254 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7257 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7248) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7251 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7254], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7254) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7251)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7254) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7248)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7254) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7248)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_right mul_le_of_le_one_rightₓ'. -/
theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align mul_le_of_le_one_right mul_le_of_le_one_right

/- warning: le_mul_of_one_le_right -> le_mul_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7315 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7318 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7321 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7324 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7315) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7318 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7321], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7321) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7318)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7321) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7315))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7321) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7315)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_right le_mul_of_one_le_rightₓ'. -/
theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align le_mul_of_one_le_right le_mul_of_one_le_right

/- warning: mul_lt_of_lt_one_left -> mul_lt_of_lt_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7382 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7385 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7388 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7391 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7382) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7385 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7388], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7388) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7385)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7388) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7382)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7388) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7382)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_left mul_lt_of_lt_one_leftₓ'. -/
theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align mul_lt_of_lt_one_left mul_lt_of_lt_one_left

/- warning: lt_mul_of_one_lt_left -> lt_mul_of_one_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7449 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7452 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7455 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7458 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7449) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7452 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7455], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7455) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7452)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7455) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7449))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7455) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7449)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_left lt_mul_of_one_lt_leftₓ'. -/
theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align lt_mul_of_one_lt_left lt_mul_of_one_lt_left

/- warning: mul_lt_of_lt_one_right -> mul_lt_of_lt_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7516 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7519 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7522 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7525 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7516) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7519 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7522], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7522) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7519)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7522) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7516)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7522) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7516)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_right mul_lt_of_lt_one_rightₓ'. -/
theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align mul_lt_of_lt_one_right mul_lt_of_lt_one_right

/- warning: lt_mul_of_one_lt_right -> lt_mul_of_one_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7583 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7586 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7589 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7592 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7583) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7586 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7589], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7589) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7586)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7589) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7583))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7589) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7583)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_right lt_mul_of_one_lt_rightₓ'. -/
theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align lt_mul_of_one_lt_right lt_mul_of_one_lt_right

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/


/- warning: mul_le_of_le_of_le_one_of_nonneg -> mul_le_of_le_of_le_one_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7651 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7654 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7660 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7651) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7654 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7651)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7654)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7657) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7651)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one_of_nonneg mul_le_of_le_of_le_one_of_nonnegₓ'. -/
/- Yaël: What's the point of these lemmas? They just chain an existing lemma with an assumption in
all possible ways, thereby artificially inflating the API and making the truly relevant lemmas hard
to find -/
theorem mul_le_of_le_of_le_one_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a ≤ c :=
  (mul_le_of_le_one_right hb ha).trans h
#align mul_le_of_le_of_le_one_of_nonneg mul_le_of_le_of_le_one_of_nonneg

/- warning: mul_lt_of_le_of_lt_one_of_pos -> mul_lt_of_le_of_lt_one_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7698 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7701 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7707 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7698) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7701 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7698)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7701)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7704) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7698)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_posₓ'. -/
theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc
#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_pos

/- warning: mul_lt_of_lt_of_le_one_of_nonneg -> mul_lt_of_lt_of_le_one_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7745 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7748 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7754 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7745) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7748 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7745)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7748)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7751) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7745)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonnegₓ'. -/
theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h
#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonneg

/- warning: left.mul_le_one_of_le_of_le -> Left.mul_le_one_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7798 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7804 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7798 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7798)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7801) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7795))))
Case conversion may be inaccurate. Consider using '#align left.mul_le_one_of_le_of_le Left.mul_le_one_of_le_of_leₓ'. -/
/-- Assumes left covariance. -/
theorem Left.mul_le_one_of_le_of_le [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one_of_nonneg ha hb a0
#align left.mul_le_one_of_le_of_le Left.mul_le_one_of_le_of_le

/- warning: left.mul_lt_of_le_of_lt_one_of_pos -> Left.mul_lt_of_le_of_lt_one_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7846 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7852 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7846 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7846)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7849) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7843))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_of_le_of_lt_one_of_pos Left.mul_lt_of_le_of_lt_one_of_posₓ'. -/
/-- Assumes left covariance. -/
theorem Left.mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (ha : a ≤ 1) (hb : b < 1)
    (a0 : 0 < a) : a * b < 1 :=
  mul_lt_of_le_of_lt_one_of_pos ha hb a0
#align left.mul_lt_of_le_of_lt_one_of_pos Left.mul_lt_of_le_of_lt_one_of_pos

/- warning: left.mul_lt_of_lt_of_le_one_of_nonneg -> Left.mul_lt_of_lt_of_le_one_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7894 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7900 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7894 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7894)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7897) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7891))))
Case conversion may be inaccurate. Consider using '#align left.mul_lt_of_lt_of_le_one_of_nonneg Left.mul_lt_of_lt_of_le_one_of_nonnegₓ'. -/
/-- Assumes left covariance. -/
theorem Left.mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (ha : a < 1) (hb : b ≤ 1)
    (a0 : 0 ≤ a) : a * b < 1 :=
  mul_lt_of_lt_of_le_one_of_nonneg ha hb a0
#align left.mul_lt_of_lt_of_le_one_of_nonneg Left.mul_lt_of_lt_of_le_one_of_nonneg

/- warning: mul_le_of_le_of_le_one' -> mul_le_of_le_of_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7936 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7939 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7945 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7936) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7939 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7948 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7936) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7939 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7936)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7939)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7939)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7942) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7936)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'ₓ'. -/
theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha
#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'

/- warning: mul_lt_of_lt_of_le_one' -> mul_lt_of_lt_of_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7995 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7998 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8004 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7995) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7998 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8007 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7995) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7998 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7995)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7998)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7998)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8001) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7995)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'ₓ'. -/
theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'

/- warning: mul_lt_of_le_of_lt_one' -> mul_lt_of_le_of_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8054 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8057 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8063 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8054) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8057 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8066 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8054) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8057 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8054)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8057)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8057)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8060) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8054)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'ₓ'. -/
theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha
#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'

/- warning: mul_lt_of_lt_of_lt_one_of_pos -> mul_lt_of_lt_of_lt_one_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8113 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8116 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8122 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8113) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8116 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8125 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8113) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8116 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8113)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8116)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8116)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8119) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8113)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_lt_one_of_pos mul_lt_of_lt_of_lt_one_of_posₓ'. -/
theorem mul_lt_of_lt_of_lt_one_of_pos [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_lt_one_of_pos mul_lt_of_lt_of_lt_one_of_pos

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/


/- warning: le_mul_of_le_of_one_le_of_nonneg -> le_mul_of_le_of_one_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8173 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8176 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8182 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8173) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8176 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8173))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8176)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8179) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8173)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonnegₓ'. -/
theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha
#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonneg

/- warning: lt_mul_of_le_of_one_lt_of_pos -> lt_mul_of_le_of_one_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8219 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8222 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8228 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8219) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8222 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8219))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8222)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8225) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8219)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_posₓ'. -/
theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha
#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_pos

/- warning: lt_mul_of_lt_of_one_le_of_nonneg -> lt_mul_of_lt_of_one_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8265 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8268 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8274 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8265) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8268 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8265))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8268)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8271) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8265)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonnegₓ'. -/
theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha
#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonneg

/- warning: left.one_le_mul_of_le_of_le -> Left.one_le_mul_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8317 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8323 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8317 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8317)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8320) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8314)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_le_mul_of_le_of_le Left.one_le_mul_of_le_of_leₓ'. -/
/-- Assumes left covariance. -/
theorem Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le_of_nonneg ha hb a0
#align left.one_le_mul_of_le_of_le Left.one_le_mul_of_le_of_le

/- warning: left.one_lt_mul_of_le_of_lt_of_pos -> Left.one_lt_mul_of_le_of_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8365 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8371 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8365 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8365)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8368) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8362)) a b))
Case conversion may be inaccurate. Consider using '#align left.one_lt_mul_of_le_of_lt_of_pos Left.one_lt_mul_of_le_of_lt_of_posₓ'. -/
/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_le_of_lt_of_pos [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_le_of_one_lt_of_pos ha hb a0
#align left.one_lt_mul_of_le_of_lt_of_pos Left.one_lt_mul_of_le_of_lt_of_pos

/- warning: left.lt_mul_of_lt_of_one_le_of_nonneg -> Left.lt_mul_of_lt_of_one_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8413 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8419 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8413 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8413)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8416) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8410)) a b))
Case conversion may be inaccurate. Consider using '#align left.lt_mul_of_lt_of_one_le_of_nonneg Left.lt_mul_of_lt_of_one_le_of_nonnegₓ'. -/
/-- Assumes left covariance. -/
theorem Left.lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (a0 : 0 ≤ a) : 1 < a * b :=
  lt_mul_of_lt_of_one_le_of_nonneg ha hb a0
#align left.lt_mul_of_lt_of_one_le_of_nonneg Left.lt_mul_of_lt_of_one_le_of_nonneg

/- warning: le_mul_of_le_of_one_le' -> le_mul_of_le_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8455 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8458 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8464 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8455) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8458 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8467 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8455) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8458 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8455))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8458)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8458)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8461) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8455)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'ₓ'. -/
theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a) (a0 : 0 ≤ a)
    (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0
#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'

/- warning: lt_mul_of_le_of_one_lt' -> lt_mul_of_le_of_one_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8514 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8517 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8523 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8514) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8517 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8526 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8514) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8517 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8514))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8517)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8517)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8520) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8514)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'ₓ'. -/
theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0
#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'

/- warning: lt_mul_of_lt_of_one_le' -> lt_mul_of_lt_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8573 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8576 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8582 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8573) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8576 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8585 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8573) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8576 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8573))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8576)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8576)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8579) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8573)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'ₓ'. -/
theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'

/- warning: lt_mul_of_lt_of_one_lt_of_pos -> lt_mul_of_lt_of_one_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8632 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8635 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8641 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8632) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8635 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8644 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8632) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8635 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8632))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8635)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8635)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8638) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8632)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_lt_of_pos lt_mul_of_lt_of_one_lt_of_posₓ'. -/
theorem lt_mul_of_lt_of_one_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (bc : b < c)
    (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_lt_of_pos lt_mul_of_lt_of_one_lt_of_pos

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/


/- warning: mul_le_of_le_one_of_le_of_nonneg -> mul_le_of_le_one_of_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8692 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8695 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8701 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8692) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8695 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8692)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8695)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8698) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8692)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonnegₓ'. -/
theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h
#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonneg

/- warning: mul_lt_of_lt_one_of_le_of_pos -> mul_lt_of_lt_one_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8739 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8742 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8748 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8739) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8742 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8739)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8742)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8745) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8739)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_posₓ'. -/
theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h
#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_pos

/- warning: mul_lt_of_le_one_of_lt_of_nonneg -> mul_lt_of_le_one_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8786 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8789 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8795 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8786) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8789 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8786)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8789)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8792) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8786)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonnegₓ'. -/
theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h
#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonneg

/- warning: right.mul_lt_one_of_lt_of_le_of_pos -> Right.mul_lt_one_of_lt_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8839 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8845 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8839 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8839)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8842) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8836))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_lt_of_le_of_pos Right.mul_lt_one_of_lt_of_le_of_posₓ'. -/
/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (hb : b ≤ 1)
    (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_le_of_pos ha hb b0
#align right.mul_lt_one_of_lt_of_le_of_pos Right.mul_lt_one_of_lt_of_le_of_pos

/- warning: right.mul_lt_one_of_le_of_lt_of_nonneg -> Right.mul_lt_one_of_le_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8887 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8893 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8887 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8887)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8890) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8884))))
Case conversion may be inaccurate. Consider using '#align right.mul_lt_one_of_le_of_lt_of_nonneg Right.mul_lt_one_of_le_of_lt_of_nonnegₓ'. -/
/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_le_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (hb : b < 1)
    (b0 : 0 ≤ b) : a * b < 1 :=
  mul_lt_of_le_one_of_lt_of_nonneg ha hb b0
#align right.mul_lt_one_of_le_of_lt_of_nonneg Right.mul_lt_one_of_le_of_lt_of_nonneg

/- warning: mul_lt_of_lt_one_of_lt_of_pos -> mul_lt_of_lt_one_of_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8929 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8932 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8938 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8929) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8932 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8941 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8929) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8932 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8929)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8932)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8932)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8935) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8929)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_posₓ'. -/
theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_pos

/- warning: right.mul_le_one_of_le_of_le -> Right.mul_le_one_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8994 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9000 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8994 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8994)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8997) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8991))))
Case conversion may be inaccurate. Consider using '#align right.mul_le_one_of_le_of_le Right.mul_le_one_of_le_of_leₓ'. -/
/-- Assumes right covariance. -/
theorem Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le_of_nonneg ha hb b0
#align right.mul_le_one_of_le_of_le Right.mul_le_one_of_le_of_le

/- warning: mul_le_of_le_one_of_le' -> mul_le_of_le_one_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9036 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9039 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9045 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9036) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9039 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9048 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9036) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9039 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9036)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9039)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9039)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9042) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9036)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'ₓ'. -/
theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha
#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'

/- warning: mul_lt_of_lt_one_of_le' -> mul_lt_of_lt_one_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9095 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9098 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9104 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9095) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9098 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9107 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9095) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9098 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9095)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9098)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9098)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9101) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9095)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'ₓ'. -/
theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'

/- warning: mul_lt_of_le_one_of_lt' -> mul_lt_of_le_one_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9154 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9157 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9163 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9154) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9157 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9166 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9154) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9157 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9154)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9157)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9157)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9160) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9154)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt' mul_lt_of_le_one_of_lt'ₓ'. -/
theorem mul_lt_of_le_one_of_lt' [PosMulStrictMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b < c)
    (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans_le <| mul_le_of_le_one_left c0 ha
#align mul_lt_of_le_one_of_lt' mul_lt_of_le_one_of_lt'

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/


/- warning: lt_mul_of_one_lt_of_le_of_pos -> lt_mul_of_one_lt_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9214 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9217 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9223 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9214) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9217 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9214))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9217)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9220) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9214)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_posₓ'. -/
theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_pos

/- warning: lt_mul_of_one_le_of_lt_of_nonneg -> lt_mul_of_one_le_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9260 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9263 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9269 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9260) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9263 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9260))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9263)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9266) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9260)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonnegₓ'. -/
theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonneg

/- warning: lt_mul_of_one_lt_of_lt_of_pos -> lt_mul_of_one_lt_of_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9306 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9309 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9315 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9306) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9309 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9306))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9309)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9312) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9306)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_posₓ'. -/
theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_pos

/- warning: right.one_lt_mul_of_lt_of_le_of_pos -> Right.one_lt_mul_of_lt_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9358 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9364 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9358 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9358)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9361) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9355)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_lt_of_le_of_pos Right.one_lt_mul_of_lt_of_le_of_posₓ'. -/
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_le_of_pos Right.one_lt_mul_of_lt_of_le_of_pos

/- warning: right.one_lt_mul_of_le_of_lt_of_nonneg -> Right.one_lt_mul_of_le_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9406 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9412 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9406 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9406)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9409) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9403)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_le_of_lt_of_nonneg Right.one_lt_mul_of_le_of_lt_of_nonnegₓ'. -/
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (b0 : 0 ≤ b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt_of_nonneg ha hb b0
#align right.one_lt_mul_of_le_of_lt_of_nonneg Right.one_lt_mul_of_le_of_lt_of_nonneg

/- warning: right.one_lt_mul_of_lt_of_lt -> Right.one_lt_mul_of_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9454 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9460 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9454 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9454)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9457) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9451)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_lt_mul_of_lt_of_lt Right.one_lt_mul_of_lt_of_ltₓ'. -/
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_lt Right.one_lt_mul_of_lt_of_lt

/- warning: lt_mul_of_one_lt_of_lt_of_nonneg -> lt_mul_of_one_lt_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9496 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9499 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9505 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9496) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9499 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9496))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9499)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9502) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9496)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonnegₓ'. -/
theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonneg

/- warning: lt_of_mul_lt_of_one_le_of_nonneg_left -> lt_of_mul_lt_of_one_le_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9542 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9545 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9551 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9542) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9545 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9542)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9542))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9545)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9548) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_leftₓ'. -/
theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h
#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_of_nonneg_left -> lt_of_lt_mul_of_le_one_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9589 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9592 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9598 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9589) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9592 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9589)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9589)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9592)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9595) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_leftₓ'. -/
theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc
#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_of_nonneg_right -> lt_of_lt_mul_of_le_one_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9635 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9638 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9644 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9635) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9638 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9635)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9635)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9638)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9641) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_rightₓ'. -/
theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb
#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_right

/- warning: le_mul_of_one_le_of_le_of_nonneg -> le_mul_of_one_le_of_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9681 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9684 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9690 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9681) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9684 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9681))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9684)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9687) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9681)) a c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonnegₓ'. -/
theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha
#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonneg

/- warning: right.one_le_mul_of_le_of_le -> Right.one_le_mul_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9733 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9739 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9733 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9733)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9736) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9730)) a b))
Case conversion may be inaccurate. Consider using '#align right.one_le_mul_of_le_of_le Right.one_le_mul_of_le_of_leₓ'. -/
/-- Assumes right covariance. -/
theorem Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le_of_nonneg ha hb b0
#align right.one_le_mul_of_le_of_le Right.one_le_mul_of_le_of_le

/- warning: le_of_mul_le_of_one_le_of_nonneg_left -> le_of_mul_le_of_one_le_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9775 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9778 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9784 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9775) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9778 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9775)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9775))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9778)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9781) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_leftₓ'. -/
theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h
#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_left

/- warning: le_of_le_mul_of_le_one_of_nonneg_left -> le_of_le_mul_of_le_one_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9822 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9825 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9831 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9822) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9825 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9822)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9822)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9825)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9828) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_leftₓ'. -/
theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc
#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_left

/- warning: le_of_mul_le_of_one_le_nonneg_right -> le_of_mul_le_of_one_le_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9868 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9871 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9877 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9868) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9871 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9868)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9868))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9871)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9874) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_rightₓ'. -/
theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h
#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_right

/- warning: le_of_le_mul_of_le_one_of_nonneg_right -> le_of_le_mul_of_le_one_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9915 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9918 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9924 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9915) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9918 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9915)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9915)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9918)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9921) a c)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_of_nonneg_right le_of_le_mul_of_le_one_of_nonneg_rightₓ'. -/
theorem le_of_le_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a ≤ c :=
  h.trans <| mul_le_of_le_one_left hc hb
#align le_of_le_mul_of_le_one_of_nonneg_right le_of_le_mul_of_le_one_of_nonneg_right

end Preorder

section LinearOrder

variable [LinearOrder α]

/- warning: exists_square_le' -> exists_square_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : LinearOrder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_3))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_3))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Exists.{succ u_1} α (fun (b : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_3))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b b) a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9979 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9982 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9985 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9988 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9979) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9982 (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9985))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9985))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9982)) a) -> (Exists.{succ u_1} α (fun (b : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9985))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9979)) b b) a))
Case conversion may be inaccurate. Consider using '#align exists_square_le' exists_square_le'ₓ'. -/
-- Yaël: What's the point of this lemma? If we have `0 * 0 = 0`, then we can just take `b = 0`.
-- proven with `a0 : 0 ≤ a` as `exists_square_le`
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a := by
  obtain ha | ha := lt_or_le a 1
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
  · exact ⟨1, by rwa [mul_one]⟩
#align exists_square_le' exists_square_le'

end LinearOrder

end MulOneClass

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

/- warning: pos_mul_mono.to_pos_mul_strict_mono -> PosMulMono.toPosMulStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10110 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10113 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10116 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10110)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10110)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10113)], PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10110)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10110)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10113)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMonoₓ'. -/
theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne (h.Ne ∘ mul_left_cancel₀ x.2.ne')⟩
#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMono

/- warning: pos_mul_mono_iff_pos_mul_strict_mono -> posMulMono_iff_posMulStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10153 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10156 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10153)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10153)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10156)) (PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10153)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10153)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10156))
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMonoₓ'. -/
theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩
#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMono

/- warning: mul_pos_mono.to_mul_pos_strict_mono -> MulPosMono.toMulPosStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10182 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10185 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10188 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10182)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10182)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10185)], MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10182)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10182)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10185)
Case conversion may be inaccurate. Consider using '#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMonoₓ'. -/
theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne (h.Ne ∘ mul_right_cancel₀ x.2.ne')⟩
#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMono

/- warning: mul_pos_mono_iff_mul_pos_strict_mono -> mulPosMono_iff_mulPosStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10225 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10228 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10225)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10225)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10228)) (MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10225)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10225)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10228))
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMonoₓ'. -/
theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩
#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMono

/- warning: pos_mul_reflect_lt.to_pos_mul_mono_rev -> PosMulReflectLT.toPosMulMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10254 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10257 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10260 : PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10254)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10254)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10257)], PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10254)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10254)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10257)
Case conversion may be inaccurate. Consider using '#align pos_mul_reflect_lt.to_pos_mul_mono_rev PosMulReflectLT.toPosMulMonoRevₓ'. -/
theorem PosMulReflectLT.toPosMulMonoRev [PosMulReflectLT α] : PosMulMonoRev α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.Ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le⟩
#align pos_mul_reflect_lt.to_pos_mul_mono_rev PosMulReflectLT.toPosMulMonoRev

/- warning: pos_mul_mono_rev_iff_pos_mul_reflect_lt -> posMulMonoRev_iff_posMulReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10301 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10304 : PartialOrder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10301)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10301)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10304)) (PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10301)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10301)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10304))
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulMonoRev_iff_posMulReflectLTₓ'. -/
theorem posMulMonoRev_iff_posMulReflectLT : PosMulMonoRev α ↔ PosMulReflectLT α :=
  ⟨@PosMulMonoRev.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulMonoRev α _ _⟩
#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulMonoRev_iff_posMulReflectLT

/- warning: mul_pos_reflect_lt.to_mul_pos_mono_rev -> MulPosReflectLT.toMulPosMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10330 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10333 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10336 : MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10330)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10330)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10333)], MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10330)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10330)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10333)
Case conversion may be inaccurate. Consider using '#align mul_pos_reflect_lt.to_mul_pos_mono_rev MulPosReflectLT.toMulPosMonoRevₓ'. -/
theorem MulPosReflectLT.toMulPosMonoRev [MulPosReflectLT α] : MulPosMonoRev α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.Ne.symm) fun h' =>
      (lt_of_mul_lt_mul_right h' x.2.le).le⟩
#align mul_pos_reflect_lt.to_mul_pos_mono_rev MulPosReflectLT.toMulPosMonoRev

/- warning: mul_pos_mono_rev_iff_mul_pos_reflect_lt -> mulPosMonoRev_iff_mulPosReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10377 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10380 : PartialOrder.{u_1} α], Iff (MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10377)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10377)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10380)) (MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10377)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10377)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10380))
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_rev_iff_mul_pos_reflect_lt mulPosMonoRev_iff_mulPosReflectLTₓ'. -/
theorem mulPosMonoRev_iff_mulPosReflectLT : MulPosMonoRev α ↔ MulPosReflectLT α :=
  ⟨@MulPosMonoRev.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosMonoRev α _ _⟩
#align mul_pos_mono_rev_iff_mul_pos_reflect_lt mulPosMonoRev_iff_mulPosReflectLT

end PartialOrder

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [CommSemigroup α] [Zero α] [Preorder α]

/- warning: pos_mul_strict_mono_iff_mul_pos_strict_mono -> posMulStrictMono_iff_mulPosStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulStrictMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosStrictMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10424 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10427 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10430 : Preorder.{u_1} α], Iff (PosMulStrictMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10424)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10427 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10430) (MulPosStrictMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10424)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10427 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10430)
Case conversion may be inaccurate. Consider using '#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMonoₓ'. -/
theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp! only [mul_comm]
#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMono

/- warning: pos_mul_reflect_lt_iff_mul_pos_reflect_lt -> posMulReflectLT_iff_mulPosReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosReflectLT.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10451 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10454 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10457 : Preorder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10451)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10454 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10457) (MulPosReflectLT.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10451)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10454 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10457)
Case conversion may be inaccurate. Consider using '#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLTₓ'. -/
theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp! only [mul_comm]
#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLT

/- warning: pos_mul_mono_iff_mul_pos_mono -> posMulMono_iff_mulPosMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10478 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10481 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10484 : Preorder.{u_1} α], Iff (PosMulMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10478)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10481 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10484) (MulPosMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10478)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10481 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10484)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMonoₓ'. -/
theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by simp! only [mul_comm]
#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMono

/- warning: pos_mul_mono_rev_iff_mul_pos_mono_rev -> posMulMonoRev_iff_mulPosMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosMonoRev.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10505 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10508 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10511 : Preorder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10505)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10508 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10511) (MulPosMonoRev.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10505)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10508 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10511)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulMonoRev_iff_mulPosMonoRevₓ'. -/
theorem posMulMonoRev_iff_mulPosMonoRev : PosMulMonoRev α ↔ MulPosMonoRev α := by
  simp! only [mul_comm]
#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulMonoRev_iff_mulPosMonoRev

end CommSemigroupHasZero

