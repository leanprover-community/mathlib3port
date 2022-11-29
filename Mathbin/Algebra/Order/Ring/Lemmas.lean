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

#print PosMulStrictMono.to_pos_mul_mono_rev /-
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.to_pos_mul_mono_rev [PosMulStrictMono α] :
    PosMulMonoRev α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_left h' x.Prop⟩
#align pos_mul_strict_mono.to_pos_mul_mono_rev PosMulStrictMono.to_pos_mul_mono_rev
-/

#print MulPosStrictMono.to_mul_pos_mono_rev /-
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.to_mul_pos_mono_rev [MulPosStrictMono α] :
    MulPosMonoRev α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_right h' x.Prop⟩
#align mul_pos_strict_mono.to_mul_pos_mono_rev MulPosStrictMono.to_mul_pos_mono_rev
-/

#print PosMulMonoRev.to_pos_mul_strict_mono /-
theorem PosMulMonoRev.to_pos_mul_strict_mono [PosMulMonoRev α] : PosMulStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_left h' x.Prop⟩
#align pos_mul_mono_rev.to_pos_mul_strict_mono PosMulMonoRev.to_pos_mul_strict_mono
-/

#print MulPosMonoRev.to_mul_pos_strict_mono /-
theorem MulPosMonoRev.to_mul_pos_strict_mono [MulPosMonoRev α] : MulPosStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_right h' x.Prop⟩
#align mul_pos_mono_rev.to_mul_pos_strict_mono MulPosMonoRev.to_mul_pos_strict_mono
-/

#print pos_mul_strict_mono_iff_pos_mul_mono_rev /-
theorem pos_mul_strict_mono_iff_pos_mul_mono_rev : PosMulStrictMono α ↔ PosMulMonoRev α :=
  ⟨@PosMulStrictMono.to_pos_mul_mono_rev _ _ _ _, @PosMulMonoRev.to_pos_mul_strict_mono _ _ _ _⟩
#align pos_mul_strict_mono_iff_pos_mul_mono_rev pos_mul_strict_mono_iff_pos_mul_mono_rev
-/

#print mul_pos_strict_mono_iff_mul_pos_mono_rev /-
theorem mul_pos_strict_mono_iff_mul_pos_mono_rev : MulPosStrictMono α ↔ MulPosMonoRev α :=
  ⟨@MulPosStrictMono.to_mul_pos_mono_rev _ _ _ _, @MulPosMonoRev.to_mul_pos_strict_mono _ _ _ _⟩
#align mul_pos_strict_mono_iff_mul_pos_mono_rev mul_pos_strict_mono_iff_mul_pos_mono_rev
-/

#print PosMulReflectLT.to_pos_mul_mono /-
theorem PosMulReflectLT.to_pos_mul_mono [PosMulReflectLT α] : PosMulMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_left h' x.Prop⟩
#align pos_mul_reflect_lt.to_pos_mul_mono PosMulReflectLT.to_pos_mul_mono
-/

#print MulPosReflectLT.to_mul_pos_mono /-
theorem MulPosReflectLT.to_mul_pos_mono [MulPosReflectLT α] : MulPosMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_right h' x.Prop⟩
#align mul_pos_reflect_lt.to_mul_pos_mono MulPosReflectLT.to_mul_pos_mono
-/

#print PosMulMono.to_pos_mul_reflect_lt /-
theorem PosMulMono.to_pos_mul_reflect_lt [PosMulMono α] : PosMulReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_left h' x.Prop⟩
#align pos_mul_mono.to_pos_mul_reflect_lt PosMulMono.to_pos_mul_reflect_lt
-/

#print MulPosMono.to_mul_pos_reflect_lt /-
theorem MulPosMono.to_mul_pos_reflect_lt [MulPosMono α] : MulPosReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_right h' x.Prop⟩
#align mul_pos_mono.to_mul_pos_reflect_lt MulPosMono.to_mul_pos_reflect_lt
-/

#print pos_mul_mono_iff_pos_mul_reflect_lt /-
theorem pos_mul_mono_iff_pos_mul_reflect_lt : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.to_pos_mul_reflect_lt _ _ _ _, @PosMulReflectLT.to_pos_mul_mono _ _ _ _⟩
#align pos_mul_mono_iff_pos_mul_reflect_lt pos_mul_mono_iff_pos_mul_reflect_lt
-/

#print mul_pos_mono_iff_mul_pos_reflect_lt /-
theorem mul_pos_mono_iff_mul_pos_reflect_lt : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.to_mul_pos_reflect_lt _ _ _ _, @MulPosReflectLT.to_mul_pos_mono _ _ _ _⟩
#align mul_pos_mono_iff_mul_pos_reflect_lt mul_pos_mono_iff_mul_pos_reflect_lt
-/

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
        
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h
        ⟩⟩
#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_pos

/- warning: mul_pos_mono_iff_covariant_pos -> mulPosMono_iff_covariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) y ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951)) (CovariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948)) y (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4948))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4961) x)) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4990 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4992 : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4951)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4990 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.4992))
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_posₓ'. -/
theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.toCovariantClassPosMulLE _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simp only [ha, mul_zero]
        
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h
        ⟩⟩
#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_pos

/- warning: pos_mul_reflect_lt_iff_contravariant_pos -> posMulReflectLT_iff_contravariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x) y) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093 : PartialOrder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090)) (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5090))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5103) x) y) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5132 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5134 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5093)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5132 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5134))
Case conversion may be inaccurate. Consider using '#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_posₓ'. -/
theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.toContravariantClassPosMulLT _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
        
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h
        ⟩⟩
#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_pos

/- warning: mul_pos_reflect_lt_iff_contravariant_pos -> mulPosReflectLT_iff_contravariant_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (fun (x : Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) y ((fun (a : Sort.{max 1 (succ u_1)}) (b : Type.{u_1}) [self : HasLiftT.{max 1 (succ u_1), succ u_1} a b] => self.0) (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (HasLiftT.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.coe.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (CoeTCₓ.mk.{max 1 (succ u_1), succ u_1} (Subtype.{succ u_1} α (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x)) α (Subtype.val.{succ u_1} α (fun (x : α) => (fun (x : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) x) x))))) x)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2))))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235 : PartialOrder.{u_1} α], Iff (MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235)) (ContravariantClass.{u_1, u_1} (Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245)) α (fun (x : Subtype.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245)) (y : α) => HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232)) y (Subtype.val.{succ u_1} α (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5232))) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5245) x)) (fun (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5274 : α) (x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5276 : α) => LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5235)) x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5274 x._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5276))
Case conversion may be inaccurate. Consider using '#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_posₓ'. -/
theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.toContravariantClassPosMulLT _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
        
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h
        ⟩⟩
#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_pos

/- warning: pos_mul_strict_mono.to_pos_mul_mono -> PosMulStrictMono.toPosMulMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5377 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5380 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5383 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5377) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5377) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5380)], PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5377) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5377) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5380)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5426 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5429 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5432 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5426) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5426) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5429)], MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5426) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5426) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5429)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5475 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5478 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5481 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5475) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5475) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5478)], PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5475) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5475) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5478)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5520 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5523 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5526 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5520) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5520) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5523)], MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5520) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5520) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5523)
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5565 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5568 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5565)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5565)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562))) a) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5562)) a c)) (Eq.{succ u_1} α b c))
Case conversion may be inaccurate. Consider using '#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_posₓ'. -/
theorem mul_left_cancel_iff_of_pos [PosMulMonoRev α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <| le_of_mul_le_mul_of_pos_left h.ge a0,
    congr_arg _⟩
#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_pos

/- warning: mul_right_cancel_iff_of_pos -> mul_right_cancel_iff_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α _inst_2)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α _inst_2)) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) c b)) (Eq.{succ u_1} α a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5620 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5623 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5620)], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5620)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617))) b) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617)) a b) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5617)) c b)) (Eq.{succ u_1} α a c))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5689 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5692 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5695 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5698 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5686)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683))) d) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5683)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} {d : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5839 : PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5842 : MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5845 : PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5848 : MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)], (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)) a b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)) c d) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5836)) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833))) c) -> (Iff (Eq.{succ u_1} α (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833)) a c) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5833)) b d)) (And (Eq.{succ u_1} α a b) (Eq.{succ u_1} α c d)))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6004 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6007 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998)) a b)) -> (Or (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998))) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998))) b)) (And (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6001))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.5998))))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6145 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6148 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6142))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6139))))
Case conversion may be inaccurate. Consider using '#align neg_of_mul_pos_right neg_of_mul_pos_rightₓ'. -/
theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2
#align neg_of_mul_pos_right neg_of_mul_pos_right

/- warning: neg_of_mul_pos_left -> neg_of_mul_pos_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6193 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6196 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187)) a b)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6190))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6187))))
Case conversion may be inaccurate. Consider using '#align neg_of_mul_pos_left neg_of_mul_pos_leftₓ'. -/
theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1
#align neg_of_mul_pos_left neg_of_mul_pos_left

/- warning: neg_iff_neg_of_mul_pos -> neg_iff_neg_of_mul_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))] [_inst_4 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6241 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238))] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6244 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235)) a b)) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235)))) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6238))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6235)))))
Case conversion may be inaccurate. Consider using '#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_posₓ'. -/
theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩
#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_pos

/- warning: left.neg_of_mul_neg_left -> Left.neg_of_mul_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6293 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6296 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6293))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6293))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6293))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6293))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6290))))
Case conversion may be inaccurate. Consider using '#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_leftₓ'. -/
theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h
#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_left

/- warning: right.neg_of_mul_neg_left -> Right.neg_of_mul_neg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) b (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6346 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6349 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6346))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6346))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6346))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6346))) b (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6343))))
Case conversion may be inaccurate. Consider using '#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_leftₓ'. -/
theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h
#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_left

/- warning: left.neg_of_mul_neg_right -> Left.neg_of_mul_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6399 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6402 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6399))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6399))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6399))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6399))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6396))))
Case conversion may be inaccurate. Consider using '#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_rightₓ'. -/
theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h
#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_right

/- warning: right.neg_of_mul_neg_right -> Right.neg_of_mul_neg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulZeroClass.{u_1} α] [_inst_2 : LinearOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1) (MulZeroClass.toHasZero.{u_1} α _inst_1) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α _inst_2))) a (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α (MulZeroClass.toHasZero.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449 : MulZeroClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6452 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6455 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449) (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449) (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6452))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6452))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulZeroClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449)) a b) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6452))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6452))) a (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α (MulZeroClass.toZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6449))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6534 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6537 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6543 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6534) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6537 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6546 : PosMulMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6534) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6537 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6537)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6534)) a b)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6540) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6534))) b))
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_right le_mul_iff_one_le_rightₓ'. -/
@[simp]
theorem le_mul_iff_one_le_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align le_mul_iff_one_le_right le_mul_iff_one_le_right

/- warning: lt_mul_iff_one_lt_right -> lt_mul_iff_one_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6610 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6613 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6619 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6610) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6613 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6622 : PosMulReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6610) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6613 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6613)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6610)) a b)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6616) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6610))) b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6686 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6689 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6695 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6686) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6689 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6698 : PosMulMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6686) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6689 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6689)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6686)) a b) a) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6692) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6686)))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_right mul_le_iff_le_one_rightₓ'. -/
@[simp]
theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulMonoRev α] (a0 : 0 < a) : a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align mul_le_iff_le_one_right mul_le_iff_le_one_right

/- warning: mul_lt_iff_lt_one_right -> mul_lt_iff_lt_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : PosMulReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6762 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6765 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6771 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6762) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6765 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6774 : PosMulReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6762) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6765 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6765)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6762)) a b) a) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6768) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6762)))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6839 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6842 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6848 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6839) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6842 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6851 : MulPosMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6839) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6842 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6842)) a) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6839)) b a)) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6845) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6839))) b))
Case conversion may be inaccurate. Consider using '#align le_mul_iff_one_le_left le_mul_iff_one_le_leftₓ'. -/
@[simp]
theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosMonoRev α] (a0 : 0 < a) : a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)
#align le_mul_iff_one_le_left le_mul_iff_one_le_left

/- warning: lt_mul_iff_one_lt_left -> lt_mul_iff_one_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6915 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6918 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6924 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6915) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6918 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6927 : MulPosReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6915) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6918 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6918)) a) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6915)) b a)) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6921) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6915))) b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6991 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6994 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7000 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6991) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6994 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7003 : MulPosMonoRev.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6991) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6994 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6994)) b) -> (Iff (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6991)) a b) b) (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6997) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.6991)))))
Case conversion may be inaccurate. Consider using '#align mul_le_iff_le_one_left mul_le_iff_le_one_leftₓ'. -/
@[simp]
theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosMonoRev α] (b0 : 0 < b) : a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)
#align mul_le_iff_le_one_left mul_le_iff_le_one_left

/- warning: mul_lt_iff_lt_one_left -> mul_lt_iff_lt_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosReflectLT.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7067 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7070 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7076 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7067) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7070 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7079 : MulPosReflectLT.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7067) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7070 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7070)) b) -> (Iff (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7067)) a b) b) (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7073) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7067)))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7144 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7147 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7150 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7153 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7144) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7147 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7150], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7150) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7147)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7150) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7144)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7150) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7144)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_left mul_le_of_le_one_leftₓ'. -/
theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align mul_le_of_le_one_left mul_le_of_le_one_left

/- warning: le_mul_of_one_le_left -> le_mul_of_one_le_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7211 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7214 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7217 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7220 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7211) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7214 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7217], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7217) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7214)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7217) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7211))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7217) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7211)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_left le_mul_of_one_le_leftₓ'. -/
theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align le_mul_of_one_le_left le_mul_of_one_le_left

/- warning: mul_le_of_le_one_right -> mul_le_of_le_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7278 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7281 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7284 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7287 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7278) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7281 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7284], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7284) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7281)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7284) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7278)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7284) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7278)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_right mul_le_of_le_one_rightₓ'. -/
theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align mul_le_of_le_one_right mul_le_of_le_one_right

/- warning: le_mul_of_one_le_right -> le_mul_of_one_le_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7345 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7348 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7351 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7354 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7345) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7348 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7351], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7351) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7348)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7351) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7345))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7351) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7345)) a b))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_right le_mul_of_one_le_rightₓ'. -/
theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align le_mul_of_one_le_right le_mul_of_one_le_right

/- warning: mul_lt_of_lt_one_left -> mul_lt_of_lt_one_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7412 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7415 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7418 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7421 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7412) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7415 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7418], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7418) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7415)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7418) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7412)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7418) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7412)) a b) b)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_left mul_lt_of_lt_one_leftₓ'. -/
theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align mul_lt_of_lt_one_left mul_lt_of_lt_one_left

/- warning: lt_mul_of_one_lt_left -> lt_mul_of_one_lt_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7479 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7482 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7485 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7488 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7479) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7482 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7485], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7485) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7482)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7485) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7479))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7485) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7479)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_left lt_mul_of_one_lt_leftₓ'. -/
theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align lt_mul_of_one_lt_left lt_mul_of_one_lt_left

/- warning: mul_lt_of_lt_one_right -> mul_lt_of_lt_one_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) a)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7546 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7549 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7552 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7555 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7546) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7549 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7552], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7552) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7549)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7552) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7546)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7552) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7546)) a b) a)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_right mul_lt_of_lt_one_rightₓ'. -/
theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align mul_lt_of_lt_one_right mul_lt_of_lt_one_right

/- warning: lt_mul_of_one_lt_right -> lt_mul_of_one_lt_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7613 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7616 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7619 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7622 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7613) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7616 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7619], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7619) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7616)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7619) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7613))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7619) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7613)) a b))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_right lt_mul_of_one_lt_rightₓ'. -/
theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align lt_mul_of_one_lt_right lt_mul_of_one_lt_right

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/


/- warning: mul_le_of_le_of_le_one_of_nonneg -> mul_le_of_le_of_le_one_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7681 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7684 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7690 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7681) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7684 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7681)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7684)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7687) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7681)) b a) c)
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7728 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7731 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7737 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7728) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7731 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7728)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7731)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7734) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7728)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_posₓ'. -/
theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc
#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_pos

/- warning: mul_lt_of_lt_of_le_one_of_nonneg -> mul_lt_of_lt_of_le_one_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7775 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7778 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7784 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7775) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7778 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7775)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7778)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7781) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7775)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonnegₓ'. -/
theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h
#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonneg

/- warning: left.mul_le_one_of_le_of_le -> Left.mul_le_one_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7828 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7834 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7828 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7828)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7831) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7825))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7876 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7882 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7876 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7876)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7879) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7873))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7924 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7930 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7924 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7924)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7927) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7921))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7966 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7969 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7975 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7966) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7969 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7978 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7966) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7969 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7966)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7969)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7969)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7972) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.7966)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'ₓ'. -/
theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha
#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'

/- warning: mul_lt_of_lt_of_le_one' -> mul_lt_of_lt_of_le_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8025 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8028 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8034 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8025) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8028 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8037 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8025) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8028 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8025)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8028)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8028)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8031) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8025)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'ₓ'. -/
theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'

/- warning: mul_lt_of_le_of_lt_one' -> mul_lt_of_le_of_lt_one' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8084 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8087 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8093 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8084) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8087 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8096 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8084) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8087 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8084)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8087)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8087)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8090) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8084)) b a) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'ₓ'. -/
theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha
#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'

/- warning: mul_lt_of_lt_of_lt_one_of_pos -> mul_lt_of_lt_of_lt_one_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b a) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8143 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8146 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8152 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8143) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8146 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8155 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8143) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8146 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8143)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8146)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8146)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8149) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8143)) b a) c)
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8203 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8206 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8212 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8203) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8206 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8203))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8206)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8209) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8203)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonnegₓ'. -/
theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha
#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonneg

/- warning: lt_mul_of_le_of_one_lt_of_pos -> lt_mul_of_le_of_one_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8249 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8252 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8258 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8249) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8252 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8249))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8252)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8255) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8249)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_posₓ'. -/
theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha
#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_pos

/- warning: lt_mul_of_lt_of_one_le_of_nonneg -> lt_mul_of_lt_of_one_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8295 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8298 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8304 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8295) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8298 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8295))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8298)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8301) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8295)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonnegₓ'. -/
theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha
#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonneg

/- warning: left.one_le_mul_of_le_of_le -> Left.one_le_mul_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8347 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8353 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8347 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8347)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8350) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8344)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8395 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8401 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8395 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8395)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8398) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8392)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8443 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8449 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8443 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8443)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8446) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8440)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8485 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8488 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8494 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8485) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8488 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8497 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8485) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8488 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8485))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8488)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8488)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8491) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8485)) c a))
Case conversion may be inaccurate. Consider using '#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'ₓ'. -/
theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a) (a0 : 0 ≤ a)
    (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0
#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'

/- warning: lt_mul_of_le_of_one_lt' -> lt_mul_of_le_of_one_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8544 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8547 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8553 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8544) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8547 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8556 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8544) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8547 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8544))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8547)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8547)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8550) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8544)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'ₓ'. -/
theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0
#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'

/- warning: lt_mul_of_lt_of_one_le' -> lt_mul_of_lt_of_one_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8603 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8606 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8612 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8603) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8606 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8615 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8603) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8606 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8603))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8606)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8606)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8609) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8603)) c a))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'ₓ'. -/
theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'

/- warning: lt_mul_of_lt_of_one_lt_of_pos -> lt_mul_of_lt_of_one_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) c a))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8662 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8665 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8671 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8662) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8665 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8674 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8662) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8665 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8662))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8665)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8665)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8668) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8662)) c a))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8722 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8725 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8731 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8722) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8725 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8722)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8725)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8728) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8722)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonnegₓ'. -/
theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h
#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonneg

/- warning: mul_lt_of_lt_one_of_le_of_pos -> mul_lt_of_lt_one_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8769 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8772 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8778 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8769) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8772 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8769)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8772)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8775) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8769)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_posₓ'. -/
theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h
#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_pos

/- warning: mul_lt_of_le_one_of_lt_of_nonneg -> mul_lt_of_le_one_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8816 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8819 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8825 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8816) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8819 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8816)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8819)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8822) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8816)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonnegₓ'. -/
theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h
#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonneg

/- warning: right.mul_lt_one_of_lt_of_le_of_pos -> Right.mul_lt_one_of_lt_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8869 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8875 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8869 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8869)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8872) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8866))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8917 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8923 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8917 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8917)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8920) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8914))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8959 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8962 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8968 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8959) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8962 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8971 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8959) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8962 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8959)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8962)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8962)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8965) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.8959)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_posₓ'. -/
theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_pos

/- warning: right.mul_le_one_of_le_of_le -> Right.mul_le_one_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9024 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9030 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9024 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9024)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9027) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021)) a b) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9021))))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9066 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9069 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9075 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9066) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9069 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9078 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9066) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9069 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9066)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9069)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9069)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9072) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9066)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'ₓ'. -/
theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha
#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'

/- warning: mul_lt_of_lt_one_of_le' -> mul_lt_of_lt_one_of_le' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9125 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9128 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9134 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9125) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9128 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9137 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9125) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9128 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9125)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9128)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9128)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9131) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9125)) a b) c)
Case conversion may be inaccurate. Consider using '#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'ₓ'. -/
theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'

/- warning: mul_lt_of_le_one_of_lt' -> mul_lt_of_le_one_of_lt' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3] [_inst_5 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9184 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9187 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9193 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9184) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9187 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9196 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9184) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9187 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190) a (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9184)))) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9187)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9187)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9190) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9184)) a b) c)
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9244 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9247 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9253 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9244) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9247 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9244))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9247)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9250) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9244)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_posₓ'. -/
theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_pos

/- warning: lt_mul_of_one_le_of_lt_of_nonneg -> lt_mul_of_one_le_of_lt_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9290 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9293 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9299 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9290) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9293 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9290))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9293)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9296) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9290)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonnegₓ'. -/
theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonneg

/- warning: lt_mul_of_one_lt_of_lt_of_pos -> lt_mul_of_one_lt_of_lt_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9336 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9339 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9345 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9336) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9339 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9336))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342) b c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9339)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9342) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9336)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_posₓ'. -/
theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_pos

/- warning: right.one_lt_mul_of_lt_of_le_of_pos -> Right.one_lt_mul_of_lt_of_le_of_pos is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosStrictMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9388 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9394 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9388 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9388)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9391) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9385)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9436 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9442 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9436 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9436)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9439) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9433)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9484 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9490 : MulPosStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9484 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9484)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9487) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9481)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9526 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9529 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9535 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9526) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9529 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9526))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9529)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9532) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9526)) a c))
Case conversion may be inaccurate. Consider using '#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonnegₓ'. -/
theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonneg

/- warning: lt_of_mul_lt_of_one_le_of_nonneg_left -> lt_of_mul_lt_of_one_le_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9572 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9575 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9581 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9572) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9575 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9572)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9572))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9575)) a) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9578) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_leftₓ'. -/
theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h
#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_of_nonneg_left -> lt_of_lt_mul_of_le_one_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9619 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9622 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9628 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9619) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9622 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9619)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9619)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9622)) b) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9625) a b)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_leftₓ'. -/
theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc
#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_left

/- warning: lt_of_lt_mul_of_le_one_of_nonneg_right -> lt_of_lt_mul_of_le_one_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9665 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9668 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9674 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9665) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9668 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9665)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9665)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9668)) c) -> (LT.lt.{u_1} α (Preorder.toLT.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9671) a c)
Case conversion may be inaccurate. Consider using '#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_rightₓ'. -/
theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb
#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_right

/- warning: le_mul_of_one_le_of_le_of_nonneg -> le_mul_of_one_le_of_le_of_nonneg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a c))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9711 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9714 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9720 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9711) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9714 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9711))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717) b c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9714)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9717) b (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9711)) a c))
Case conversion may be inaccurate. Consider using '#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonnegₓ'. -/
theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha
#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonneg

/- warning: right.one_le_mul_of_le_of_le -> Right.one_le_mul_of_le_of_le is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b))
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9763 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9769 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9763 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9763)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9766) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9760)) a b))
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
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9805 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9808 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9814 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9805) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9808 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9805)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9805))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9808)) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9811) a c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_leftₓ'. -/
theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h
#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_left

/- warning: le_of_le_mul_of_le_one_of_nonneg_left -> le_of_le_mul_of_le_one_of_nonneg_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : PosMulMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) c (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a b)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9852 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9855 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9861 : PosMulMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9852) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9855 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9852)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858) c (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9852)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9855)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9858) a b)
Case conversion may be inaccurate. Consider using '#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_leftₓ'. -/
theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc
#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_left

/- warning: le_of_mul_le_of_one_le_nonneg_right -> le_of_mul_le_of_one_le_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1)))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9898 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9901 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9907 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9898) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9901 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9898)) a b) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904) (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9898))) a) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9901)) b) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9904) b c)
Case conversion may be inaccurate. Consider using '#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_rightₓ'. -/
theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h
#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_right

/- warning: le_of_le_mul_of_le_one_of_nonneg_right -> le_of_le_mul_of_le_one_of_nonneg_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [_inst_1 : MulOneClass.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α] [_inst_4 : MulPosMono.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1) _inst_2 _inst_3], (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toHasMul.{u_1} α _inst_1)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) b (OfNat.ofNat.{u_1} α 1 (OfNat.mk.{u_1} α 1 (One.one.{u_1} α (MulOneClass.toHasOne.{u_1} α _inst_1))))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) (OfNat.ofNat.{u_1} α 0 (OfNat.mk.{u_1} α 0 (Zero.zero.{u_1} α _inst_2))) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α _inst_3) a c)
but is expected to have type
  forall {α : Type.{u_1}} {a : α} {b : α} {c : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9945 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9948 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951 : Preorder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9954 : MulPosMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9945) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9948 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951], (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951) a (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9945)) b c)) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951) b (OfNat.ofNat.{u_1} α 1 (One.toOfNat1.{u_1} α (MulOneClass.toOne.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9945)))) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9948)) c) -> (LE.le.{u_1} α (Preorder.toLE.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.9951) a c)
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
  forall {α : Type.{u_1}} {a : α} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10009 : MulOneClass.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10012 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10015 : LinearOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10018 : PosMulStrictMono.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10009) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10012 (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10015))], (LT.lt.{u_1} α (Preorder.toLT.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10015))) (OfNat.ofNat.{u_1} α 0 (Zero.toOfNat0.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10012)) a) -> (Exists.{succ u_1} α (fun (b : α) => LE.le.{u_1} α (Preorder.toLE.{u_1} α (PartialOrder.toPreorder.{u_1} α (LinearOrder.toPartialOrder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10015))) (HMul.hMul.{u_1, u_1, u_1} α α α (instHMul.{u_1} α (MulOneClass.toMul.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10009)) b b) a))
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10144 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10147 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10150 : PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10144)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10144)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10147)], PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10144)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10144)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10147)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMonoₓ'. -/
theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne (h.Ne ∘ mul_left_cancel₀ x.2.ne')⟩
#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMono

/- warning: pos_mul_mono_iff_pos_mul_strict_mono -> posMulMono_iff_posMulStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (PosMulStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10187 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10190 : PartialOrder.{u_1} α], Iff (PosMulMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10187)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10187)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10190)) (PosMulStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10187)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10187)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10190))
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMonoₓ'. -/
theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩
#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMono

/- warning: mul_pos_mono.to_mul_pos_strict_mono -> MulPosMono.toMulPosStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10216 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10219 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10222 : MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10216)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10216)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10219)], MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10216)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10216)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10219)
Case conversion may be inaccurate. Consider using '#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMonoₓ'. -/
theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne (h.Ne ∘ mul_right_cancel₀ x.2.ne')⟩
#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMono

/- warning: mul_pos_mono_iff_mul_pos_strict_mono -> mulPosMono_iff_mulPosStrictMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)) (MulPosStrictMono.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2))
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10259 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10262 : PartialOrder.{u_1} α], Iff (MulPosMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10259)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10259)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10262)) (MulPosStrictMono.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10259)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10259)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10262))
Case conversion may be inaccurate. Consider using '#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMonoₓ'. -/
theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩
#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMono

/- warning: pos_mul_reflect_lt.to_pos_mul_mono_rev -> PosMulReflectLT.toPosMulMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : PosMulReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], PosMulMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10288 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10291 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10294 : PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10288)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10288)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10291)], PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10288)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10288)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10291)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10335 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10338 : PartialOrder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10335)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10335)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10338)) (PosMulReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10335)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10335)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10338))
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulMonoRev_iff_posMulReflectLTₓ'. -/
theorem posMulMonoRev_iff_posMulReflectLT : PosMulMonoRev α ↔ PosMulReflectLT α :=
  ⟨@PosMulMonoRev.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulMonoRev α _ _⟩
#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulMonoRev_iff_posMulReflectLT

/- warning: mul_pos_reflect_lt.to_mul_pos_mono_rev -> MulPosReflectLT.toMulPosMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CancelMonoidWithZero.{u_1} α] [_inst_2 : PartialOrder.{u_1} α] [_inst_3 : MulPosReflectLT.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)], MulPosMonoRev.{u_1} α (MulZeroClass.toHasMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (MulZeroClass.toHasZero.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α _inst_1)))) (PartialOrder.toPreorder.{u_1} α _inst_2)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10364 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10367 : PartialOrder.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10370 : MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10364)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10364)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10367)], MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10364)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10364)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10367)
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10411 : CancelMonoidWithZero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10414 : PartialOrder.{u_1} α], Iff (MulPosMonoRev.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10411)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10411)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10414)) (MulPosReflectLT.{u_1} α (MulZeroClass.toMul.{u_1} α (MulZeroOneClass.toMulZeroClass.{u_1} α (MonoidWithZero.toMulZeroOneClass.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10411)))) (MonoidWithZero.toZero.{u_1} α (CancelMonoidWithZero.toMonoidWithZero.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10411)) (PartialOrder.toPreorder.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10414))
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
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10458 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10461 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10464 : Preorder.{u_1} α], Iff (PosMulStrictMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10458)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10461 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10464) (MulPosStrictMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10458)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10461 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10464)
Case conversion may be inaccurate. Consider using '#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMonoₓ'. -/
theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp! only [mul_comm]
#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMono

/- warning: pos_mul_reflect_lt_iff_mul_pos_reflect_lt -> posMulReflectLT_iff_mulPosReflectLT is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosReflectLT.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10485 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10488 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10491 : Preorder.{u_1} α], Iff (PosMulReflectLT.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10485)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10488 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10491) (MulPosReflectLT.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10485)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10488 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10491)
Case conversion may be inaccurate. Consider using '#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLTₓ'. -/
theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp! only [mul_comm]
#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLT

/- warning: pos_mul_mono_iff_mul_pos_mono -> posMulMono_iff_mulPosMono is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosMono.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10512 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10515 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10518 : Preorder.{u_1} α], Iff (PosMulMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10512)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10515 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10518) (MulPosMono.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10512)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10515 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10518)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMonoₓ'. -/
theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by simp! only [mul_comm]
#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMono

/- warning: pos_mul_mono_rev_iff_mul_pos_mono_rev -> posMulMonoRev_iff_mulPosMonoRev is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u_1}} [_inst_1 : CommSemigroup.{u_1} α] [_inst_2 : Zero.{u_1} α] [_inst_3 : Preorder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3) (MulPosMonoRev.{u_1} α (Semigroup.toHasMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α _inst_1)) _inst_2 _inst_3)
but is expected to have type
  forall {α : Type.{u_1}} [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10539 : CommSemigroup.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10542 : Zero.{u_1} α] [inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10545 : Preorder.{u_1} α], Iff (PosMulMonoRev.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10539)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10542 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10545) (MulPosMonoRev.{u_1} α (Semigroup.toMul.{u_1} α (CommSemigroup.toSemigroup.{u_1} α inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10539)) inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10542 inst._@.Mathlib.Algebra.Order.Ring.Lemmas._hyg.10545)
Case conversion may be inaccurate. Consider using '#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulMonoRev_iff_mulPosMonoRevₓ'. -/
theorem posMulMonoRev_iff_mulPosMonoRev : PosMulMonoRev α ↔ MulPosMonoRev α := by
  simp! only [mul_comm]
#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulMonoRev_iff_mulPosMonoRev

end CommSemigroupHasZero

