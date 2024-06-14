/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa, Yuyang Zhao
-/
import Algebra.Order.Monoid.Unbundled.Defs
import Algebra.GroupWithZero.Defs

#align_import algebra.order.ring.lemmas from "leanprover-community/mathlib"@"44e29dbcff83ba7114a464d592b8c3743987c1e5"

/-!
# Multiplication by ·positive· elements is monotonic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
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

/- Notations for nonnegative and positive elements
https://
leanprover.zulipchat.com/#narrow/stream/113488-general/topic/notation.20for.20positive.20elements
-/
local notation "α≥0" => { x : α // 0 ≤ x }

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

#print PosMulReflectLE /-
/-- `pos_mul_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, x * y) (≤)`,
expressing that multiplication by positive elements on the left is reverse monotone. -/
abbrev PosMulReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => x * y) (· ≤ ·)
#align pos_mul_mono_rev PosMulReflectLE
-/

#print MulPosReflectLE /-
/-- `mul_pos_mono_rev α` is an abbreviation for `contravariant_class α>0 α (λ x y, y * x) (≤)`,
expressing that multiplication by positive elements on the right is reverse monotone. -/
abbrev MulPosReflectLE : Prop :=
  ContravariantClass α>0 α (fun x y => y * x) (· ≤ ·)
#align mul_pos_mono_rev MulPosReflectLE
-/

end Abbreviations

variable {α} {a b c d : α}

section HasMulZero

variable [Mul α] [Zero α]

section Preorder

variable [Preorder α]

#print PosMulMono.to_covariantClass_pos_mul_le /-
instance PosMulMono.to_covariantClass_pos_mul_le [PosMulMono α] :
    CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨fun a b c bc => @CovariantClass.elim α≥0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align pos_mul_mono.to_covariant_class_pos_mul_le PosMulMono.to_covariantClass_pos_mul_le
-/

#print MulPosMono.to_covariantClass_pos_mul_le /-
instance MulPosMono.to_covariantClass_pos_mul_le [MulPosMono α] :
    CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨fun a b c bc => @CovariantClass.elim α≥0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align mul_pos_mono.to_covariant_class_pos_mul_le MulPosMono.to_covariantClass_pos_mul_le
-/

#print PosMulReflectLT.to_contravariantClass_pos_mul_lt /-
instance PosMulReflectLT.to_contravariantClass_pos_mul_lt [PosMulReflectLT α] :
    ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨fun a b c bc => @ContravariantClass.elim α≥0 α (fun x y => x * y) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align pos_mul_reflect_lt.to_contravariant_class_pos_mul_lt PosMulReflectLT.to_contravariantClass_pos_mul_lt
-/

#print MulPosReflectLT.to_contravariantClass_pos_mul_lt /-
instance MulPosReflectLT.to_contravariantClass_pos_mul_lt [MulPosReflectLT α] :
    ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨fun a b c bc => @ContravariantClass.elim α≥0 α (fun x y => y * x) (· < ·) _ ⟨_, a.2.le⟩ _ _ bc⟩
#align mul_pos_reflect_lt.to_contravariant_class_pos_mul_lt MulPosReflectLT.to_contravariantClass_pos_mul_lt
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
theorem le_of_mul_le_mul_left [PosMulReflectLE α] (bc : a * b ≤ a * c) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_left le_of_mul_le_mul_left
-/

#print le_of_mul_le_mul_right /-
theorem le_of_mul_le_mul_right [MulPosReflectLE α] (bc : b * a ≤ c * a) (a0 : 0 < a) : b ≤ c :=
  @ContravariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨a, a0⟩ _ _ bc
#align le_of_mul_le_mul_right le_of_mul_le_mul_right
-/

alias lt_of_mul_lt_mul_of_nonneg_left := lt_of_mul_lt_mul_left
#align lt_of_mul_lt_mul_of_nonneg_left lt_of_mul_lt_mul_of_nonneg_left

alias lt_of_mul_lt_mul_of_nonneg_right := lt_of_mul_lt_mul_right
#align lt_of_mul_lt_mul_of_nonneg_right lt_of_mul_lt_mul_of_nonneg_right

alias le_of_mul_le_mul_of_pos_left := le_of_mul_le_mul_left
#align le_of_mul_le_mul_of_pos_left le_of_mul_le_mul_of_pos_left

alias le_of_mul_le_mul_of_pos_right := le_of_mul_le_mul_right
#align le_of_mul_le_mul_of_pos_right le_of_mul_le_mul_of_pos_right

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
theorem mul_le_mul_left [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) : a * b ≤ a * c ↔ b ≤ c :=
  @rel_iff_cov α>0 α (fun x y => x * y) (· ≤ ·) _ _ ⟨a, a0⟩ _ _
#align mul_le_mul_left mul_le_mul_left
-/

#print mul_le_mul_right /-
@[simp]
theorem mul_le_mul_right [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) : b * a ≤ c * a ↔ b ≤ c :=
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
instance (priority := 100) PosMulStrictMono.to_posMulReflectLE [PosMulStrictMono α] :
    PosMulReflectLE α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_left h' x.IProp⟩
#align pos_mul_strict_mono.to_pos_mul_mono_rev PosMulStrictMono.to_posMulReflectLE

-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.to_mulPosReflectLE [MulPosStrictMono α] :
    MulPosReflectLE α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| mul_lt_mul_of_pos_right h' x.IProp⟩
#align mul_pos_strict_mono.to_mul_pos_mono_rev MulPosStrictMono.to_mulPosReflectLE

#print PosMulReflectLE.toPosMulStrictMono /-
theorem PosMulReflectLE.toPosMulStrictMono [PosMulReflectLE α] : PosMulStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_left h' x.IProp⟩
#align pos_mul_mono_rev.to_pos_mul_strict_mono PosMulReflectLE.toPosMulStrictMono
-/

#print MulPosReflectLE.toMulPosStrictMono /-
theorem MulPosReflectLE.toMulPosStrictMono [MulPosReflectLE α] : MulPosStrictMono α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| le_of_mul_le_mul_of_pos_right h' x.IProp⟩
#align mul_pos_mono_rev.to_mul_pos_strict_mono MulPosReflectLE.toMulPosStrictMono
-/

#print posMulStrictMono_iff_posMulReflectLE /-
theorem posMulStrictMono_iff_posMulReflectLE : PosMulStrictMono α ↔ PosMulReflectLE α :=
  ⟨@PosMulStrictMono.to_posMulReflectLE _ _ _ _, @PosMulReflectLE.toPosMulStrictMono _ _ _ _⟩
#align pos_mul_strict_mono_iff_pos_mul_mono_rev posMulStrictMono_iff_posMulReflectLE
-/

#print mulPosStrictMono_iff_mulPosReflectLE /-
theorem mulPosStrictMono_iff_mulPosReflectLE : MulPosStrictMono α ↔ MulPosReflectLE α :=
  ⟨@MulPosStrictMono.to_mulPosReflectLE _ _ _ _, @MulPosReflectLE.toMulPosStrictMono _ _ _ _⟩
#align mul_pos_strict_mono_iff_mul_pos_mono_rev mulPosStrictMono_iff_mulPosReflectLE
-/

#print PosMulReflectLT.toPosMulMono /-
theorem PosMulReflectLT.toPosMulMono [PosMulReflectLT α] : PosMulMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_left h' x.IProp⟩
#align pos_mul_reflect_lt.to_pos_mul_mono PosMulReflectLT.toPosMulMono
-/

#print MulPosReflectLT.toMulPosMono /-
theorem MulPosReflectLT.toMulPosMono [MulPosReflectLT α] : MulPosMono α :=
  ⟨fun x a b h => le_of_not_lt fun h' => h.not_lt <| lt_of_mul_lt_mul_right h' x.IProp⟩
#align mul_pos_reflect_lt.to_mul_pos_mono MulPosReflectLT.toMulPosMono
-/

#print PosMulMono.toPosMulReflectLT /-
theorem PosMulMono.toPosMulReflectLT [PosMulMono α] : PosMulReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_left h' x.IProp⟩
#align pos_mul_mono.to_pos_mul_reflect_lt PosMulMono.toPosMulReflectLT
-/

#print MulPosMono.toMulPosReflectLT /-
theorem MulPosMono.toMulPosReflectLT [MulPosMono α] : MulPosReflectLT α :=
  ⟨fun x a b h => lt_of_not_le fun h' => h.not_le <| mul_le_mul_of_nonneg_right h' x.IProp⟩
#align mul_pos_mono.to_mul_pos_reflect_lt MulPosMono.toMulPosReflectLT
-/

#print posMulMono_iff_posMulReflectLT /-
theorem posMulMono_iff_posMulReflectLT : PosMulMono α ↔ PosMulReflectLT α :=
  ⟨@PosMulMono.toPosMulReflectLT _ _ _ _, @PosMulReflectLT.toPosMulMono _ _ _ _⟩
#align pos_mul_mono_iff_pos_mul_reflect_lt posMulMono_iff_posMulReflectLT
-/

#print mulPosMono_iff_mulPosReflectLT /-
theorem mulPosMono_iff_mulPosReflectLT : MulPosMono α ↔ MulPosReflectLT α :=
  ⟨@MulPosMono.toMulPosReflectLT _ _ _ _, @MulPosReflectLT.toMulPosMono _ _ _ _⟩
#align mul_pos_mono_iff_mul_pos_reflect_lt mulPosMono_iff_mulPosReflectLT
-/

end LinearOrder

end HasMulZero

section MulZeroClass

variable [MulZeroClass α]

section Preorder

variable [Preorder α]

#print Left.mul_pos /-
/-- Assumes left covariance. -/
theorem Left.mul_pos [PosMulStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [MulZeroClass.mul_zero] using mul_lt_mul_of_pos_left hb ha
#align left.mul_pos Left.mul_pos
-/

alias mul_pos := Left.mul_pos
#align mul_pos mul_pos

#print mul_neg_of_pos_of_neg /-
theorem mul_neg_of_pos_of_neg [PosMulStrictMono α] (ha : 0 < a) (hb : b < 0) : a * b < 0 := by
  simpa only [MulZeroClass.mul_zero] using mul_lt_mul_of_pos_left hb ha
#align mul_neg_of_pos_of_neg mul_neg_of_pos_of_neg
-/

#print mul_pos_iff_of_pos_left /-
@[simp]
theorem mul_pos_iff_of_pos_left [PosMulStrictMono α] [PosMulReflectLT α] (h : 0 < c) :
    0 < c * b ↔ 0 < b := by convert mul_lt_mul_left h; simp
#align zero_lt_mul_left mul_pos_iff_of_pos_left
-/

#print Right.mul_pos /-
/-- Assumes right covariance. -/
theorem Right.mul_pos [MulPosStrictMono α] (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  simpa only [MulZeroClass.zero_mul] using mul_lt_mul_of_pos_right ha hb
#align right.mul_pos Right.mul_pos
-/

#print mul_neg_of_neg_of_pos /-
theorem mul_neg_of_neg_of_pos [MulPosStrictMono α] (ha : a < 0) (hb : 0 < b) : a * b < 0 := by
  simpa only [MulZeroClass.zero_mul] using mul_lt_mul_of_pos_right ha hb
#align mul_neg_of_neg_of_pos mul_neg_of_neg_of_pos
-/

#print mul_pos_iff_of_pos_right /-
@[simp]
theorem mul_pos_iff_of_pos_right [MulPosStrictMono α] [MulPosReflectLT α] (h : 0 < c) :
    0 < b * c ↔ 0 < b := by convert mul_lt_mul_right h; simp
#align zero_lt_mul_right mul_pos_iff_of_pos_right
-/

#print Left.mul_nonneg /-
/-- Assumes left covariance. -/
theorem Left.mul_nonneg [PosMulMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [MulZeroClass.mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align left.mul_nonneg Left.mul_nonneg
-/

alias mul_nonneg := Left.mul_nonneg
#align mul_nonneg mul_nonneg

#print mul_nonpos_of_nonneg_of_nonpos /-
theorem mul_nonpos_of_nonneg_of_nonpos [PosMulMono α] (ha : 0 ≤ a) (hb : b ≤ 0) : a * b ≤ 0 := by
  simpa only [MulZeroClass.mul_zero] using mul_le_mul_of_nonneg_left hb ha
#align mul_nonpos_of_nonneg_of_nonpos mul_nonpos_of_nonneg_of_nonpos
-/

#print Right.mul_nonneg /-
/-- Assumes right covariance. -/
theorem Right.mul_nonneg [MulPosMono α] (ha : 0 ≤ a) (hb : 0 ≤ b) : 0 ≤ a * b := by
  simpa only [MulZeroClass.zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align right.mul_nonneg Right.mul_nonneg
-/

#print mul_nonpos_of_nonpos_of_nonneg /-
theorem mul_nonpos_of_nonpos_of_nonneg [MulPosMono α] (ha : a ≤ 0) (hb : 0 ≤ b) : a * b ≤ 0 := by
  simpa only [MulZeroClass.zero_mul] using mul_le_mul_of_nonneg_right ha hb
#align mul_nonpos_of_nonpos_of_nonneg mul_nonpos_of_nonpos_of_nonneg
-/

#print pos_of_mul_pos_right /-
theorem pos_of_mul_pos_right [PosMulReflectLT α] (h : 0 < a * b) (ha : 0 ≤ a) : 0 < b :=
  lt_of_mul_lt_mul_left ((MulZeroClass.mul_zero a).symm ▸ h : a * 0 < a * b) ha
#align pos_of_mul_pos_right pos_of_mul_pos_right
-/

#print pos_of_mul_pos_left /-
theorem pos_of_mul_pos_left [MulPosReflectLT α] (h : 0 < a * b) (hb : 0 ≤ b) : 0 < a :=
  lt_of_mul_lt_mul_right ((MulZeroClass.zero_mul b).symm ▸ h : 0 * b < a * b) hb
#align pos_of_mul_pos_left pos_of_mul_pos_left
-/

#print pos_iff_pos_of_mul_pos /-
theorem pos_iff_pos_of_mul_pos [PosMulReflectLT α] [MulPosReflectLT α] (hab : 0 < a * b) :
    0 < a ↔ 0 < b :=
  ⟨pos_of_mul_pos_right hab ∘ le_of_lt, pos_of_mul_pos_left hab ∘ le_of_lt⟩
#align pos_iff_pos_of_mul_pos pos_iff_pos_of_mul_pos
-/

#print mul_le_mul_of_le_of_le /-
theorem mul_le_mul_of_le_of_le [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (a0 : 0 ≤ a)
    (d0 : 0 ≤ d) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_left h₂ a0).trans <| mul_le_mul_of_nonneg_right h₁ d0
#align mul_le_mul_of_le_of_le mul_le_mul_of_le_of_le
-/

#print mul_le_mul /-
theorem mul_le_mul [PosMulMono α] [MulPosMono α] (h₁ : a ≤ b) (h₂ : c ≤ d) (c0 : 0 ≤ c)
    (b0 : 0 ≤ b) : a * c ≤ b * d :=
  (mul_le_mul_of_nonneg_right h₁ c0).trans <| mul_le_mul_of_nonneg_left h₂ b0
#align mul_le_mul mul_le_mul
-/

#print mul_self_le_mul_self /-
theorem mul_self_le_mul_self [PosMulMono α] [MulPosMono α] (ha : 0 ≤ a) (hab : a ≤ b) :
    a * a ≤ b * b :=
  mul_le_mul hab hab ha <| ha.trans hab
#align mul_self_le_mul_self mul_self_le_mul_self
-/

#print mul_le_of_mul_le_of_nonneg_left /-
theorem mul_le_of_mul_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hle : d ≤ b) (a0 : 0 ≤ a) :
    a * d ≤ c :=
  (mul_le_mul_of_nonneg_left hle a0).trans h
#align mul_le_of_mul_le_of_nonneg_left mul_le_of_mul_le_of_nonneg_left
-/

#print le_mul_of_le_mul_of_nonneg_left /-
theorem le_mul_of_le_mul_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hle : c ≤ d) (b0 : 0 ≤ b) :
    a ≤ b * d :=
  h.trans (mul_le_mul_of_nonneg_left hle b0)
#align le_mul_of_le_mul_of_nonneg_left le_mul_of_le_mul_of_nonneg_left
-/

#print mul_le_of_mul_le_of_nonneg_right /-
theorem mul_le_of_mul_le_of_nonneg_right [MulPosMono α] (h : a * b ≤ c) (hle : d ≤ a) (b0 : 0 ≤ b) :
    d * b ≤ c :=
  (mul_le_mul_of_nonneg_right hle b0).trans h
#align mul_le_of_mul_le_of_nonneg_right mul_le_of_mul_le_of_nonneg_right
-/

#print le_mul_of_le_mul_of_nonneg_right /-
theorem le_mul_of_le_mul_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hle : b ≤ d) (c0 : 0 ≤ c) :
    a ≤ d * c :=
  h.trans (mul_le_mul_of_nonneg_right hle c0)
#align le_mul_of_le_mul_of_nonneg_right le_mul_of_le_mul_of_nonneg_right
-/

end Preorder

section PartialOrder

variable [PartialOrder α]

#print posMulMono_iff_covariant_pos /-
theorem posMulMono_iff_covariant_pos :
    PosMulMono α ↔ CovariantClass α>0 α (fun x y => x * y) (· ≤ ·) :=
  ⟨@PosMulMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simp only [ha, MulZeroClass.zero_mul]
      · exact @CovariantClass.elim α>0 α (fun x y => x * y) (· ≤ ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align pos_mul_mono_iff_covariant_pos posMulMono_iff_covariant_pos
-/

#print mulPosMono_iff_covariant_pos /-
theorem mulPosMono_iff_covariant_pos :
    MulPosMono α ↔ CovariantClass α>0 α (fun x y => y * x) (· ≤ ·) :=
  ⟨@MulPosMono.to_covariantClass_pos_mul_le _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simp only [ha, MulZeroClass.mul_zero]
      · exact @CovariantClass.elim α>0 α (fun x y => y * x) (· ≤ ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align mul_pos_mono_iff_covariant_pos mulPosMono_iff_covariant_pos
-/

#print posMulReflectLT_iff_contravariant_pos /-
theorem posMulReflectLT_iff_contravariant_pos :
    PosMulReflectLT α ↔ ContravariantClass α>0 α (fun x y => x * y) (· < ·) :=
  ⟨@PosMulReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
      · exact @ContravariantClass.elim α>0 α (fun x y => x * y) (· < ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align pos_mul_reflect_lt_iff_contravariant_pos posMulReflectLT_iff_contravariant_pos
-/

#print mulPosReflectLT_iff_contravariant_pos /-
theorem mulPosReflectLT_iff_contravariant_pos :
    MulPosReflectLT α ↔ ContravariantClass α>0 α (fun x y => y * x) (· < ·) :=
  ⟨@MulPosReflectLT.to_contravariantClass_pos_mul_lt _ _ _ _, fun h =>
    ⟨fun a b c h => by
      obtain ha | ha := a.prop.eq_or_gt
      · simpa [ha] using h
      · exact @ContravariantClass.elim α>0 α (fun x y => y * x) (· < ·) _ ⟨_, ha⟩ _ _ h⟩⟩
#align mul_pos_reflect_lt_iff_contravariant_pos mulPosReflectLT_iff_contravariant_pos
-/

#print PosMulStrictMono.toPosMulMono /-
-- see Note [lower instance priority]
instance (priority := 100) PosMulStrictMono.toPosMulMono [PosMulStrictMono α] : PosMulMono α :=
  posMulMono_iff_covariant_pos.2 <|
    ⟨fun a => StrictMono.monotone <| @CovariantClass.elim _ _ _ _ _ _⟩
#align pos_mul_strict_mono.to_pos_mul_mono PosMulStrictMono.toPosMulMono
-/

#print MulPosStrictMono.toMulPosMono /-
-- see Note [lower instance priority]
instance (priority := 100) MulPosStrictMono.toMulPosMono [MulPosStrictMono α] : MulPosMono α :=
  mulPosMono_iff_covariant_pos.2 <|
    ⟨fun a => StrictMono.monotone <| @CovariantClass.elim _ _ _ _ _ _⟩
#align mul_pos_strict_mono.to_mul_pos_mono MulPosStrictMono.toMulPosMono
-/

#print PosMulReflectLE.toPosMulReflectLT /-
-- see Note [lower instance priority]
instance (priority := 100) PosMulReflectLE.toPosMulReflectLT [PosMulReflectLE α] :
    PosMulReflectLT α :=
  posMulReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_left h.le a.2).lt_of_ne <| by rintro rfl; simpa using h⟩
#align pos_mul_mono_rev.to_pos_mul_reflect_lt PosMulReflectLE.toPosMulReflectLT
-/

#print MulPosReflectLE.toMulPosReflectLT /-
-- see Note [lower instance priority]
instance (priority := 100) MulPosReflectLE.toMulPosReflectLT [MulPosReflectLE α] :
    MulPosReflectLT α :=
  mulPosReflectLT_iff_contravariant_pos.2
    ⟨fun a b c h =>
      (le_of_mul_le_mul_of_pos_right h.le a.2).lt_of_ne <| by rintro rfl; simpa using h⟩
#align mul_pos_mono_rev.to_mul_pos_reflect_lt MulPosReflectLE.toMulPosReflectLT
-/

#print mul_left_cancel_iff_of_pos /-
theorem mul_left_cancel_iff_of_pos [PosMulReflectLE α] (a0 : 0 < a) : a * b = a * c ↔ b = c :=
  ⟨fun h => (le_of_mul_le_mul_of_pos_left h.le a0).antisymm <| le_of_mul_le_mul_of_pos_left h.ge a0,
    congr_arg _⟩
#align mul_left_cancel_iff_of_pos mul_left_cancel_iff_of_pos
-/

#print mul_right_cancel_iff_of_pos /-
theorem mul_right_cancel_iff_of_pos [MulPosReflectLE α] (b0 : 0 < b) : a * b = c * b ↔ a = c :=
  ⟨fun h =>
    (le_of_mul_le_mul_of_pos_right h.le b0).antisymm <| le_of_mul_le_mul_of_pos_right h.ge b0,
    congr_arg _⟩
#align mul_right_cancel_iff_of_pos mul_right_cancel_iff_of_pos
-/

#print mul_eq_mul_iff_eq_and_eq_of_pos /-
theorem mul_eq_mul_iff_eq_and_eq_of_pos [PosMulStrictMono α] [MulPosStrictMono α]
    [PosMulReflectLE α] [MulPosReflectLE α] (hac : a ≤ b) (hbd : c ≤ d) (a0 : 0 < a) (d0 : 0 < d) :
    a * c = b * d ↔ a = b ∧ c = d :=
  by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos a0).mp h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iff_of_pos d0).mp h, rfl⟩
  exact ((mul_lt_mul_of_pos_of_pos hac hbd a0 d0).Ne h).elim
#align mul_eq_mul_iff_eq_and_eq_of_pos mul_eq_mul_iff_eq_and_eq_of_pos
-/

#print mul_eq_mul_iff_eq_and_eq_of_pos' /-
theorem mul_eq_mul_iff_eq_and_eq_of_pos' [PosMulStrictMono α] [MulPosStrictMono α]
    [PosMulReflectLE α] [MulPosReflectLE α] (hac : a ≤ b) (hbd : c ≤ d) (b0 : 0 < b) (c0 : 0 < c) :
    a * c = b * d ↔ a = b ∧ c = d :=
  by
  refine' ⟨fun h => _, fun h => congr_arg₂ (· * ·) h.1 h.2⟩
  rcases hac.eq_or_lt with (rfl | hac)
  · exact ⟨rfl, (mul_left_cancel_iff_of_pos b0).mp h⟩
  rcases eq_or_lt_of_le hbd with (rfl | hbd)
  · exact ⟨(mul_right_cancel_iff_of_pos c0).mp h, rfl⟩
  exact ((mul_lt_mul_of_lt_of_lt' hac hbd b0 c0).Ne h).elim
#align mul_eq_mul_iff_eq_and_eq_of_pos' mul_eq_mul_iff_eq_and_eq_of_pos'
-/

end PartialOrder

section LinearOrder

variable [LinearOrder α]

#print pos_and_pos_or_neg_and_neg_of_mul_pos /-
theorem pos_and_pos_or_neg_and_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) :
    0 < a ∧ 0 < b ∨ a < 0 ∧ b < 0 :=
  by
  rcases lt_trichotomy 0 a with (ha | rfl | ha)
  · refine' Or.inl ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonneg_of_nonpos ha.le hb
  · rw [MulZeroClass.zero_mul] at hab; exact hab.false.elim
  · refine' Or.inr ⟨ha, lt_imp_lt_of_le_imp_le (fun hb => _) hab⟩
    exact mul_nonpos_of_nonpos_of_nonneg ha.le hb
#align pos_and_pos_or_neg_and_neg_of_mul_pos pos_and_pos_or_neg_and_neg_of_mul_pos
-/

#print neg_of_mul_pos_right /-
theorem neg_of_mul_pos_right [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : a ≤ 0) : b < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.1.not_le ha).2
#align neg_of_mul_pos_right neg_of_mul_pos_right
-/

#print neg_of_mul_pos_left /-
theorem neg_of_mul_pos_left [PosMulMono α] [MulPosMono α] (h : 0 < a * b) (ha : b ≤ 0) : a < 0 :=
  ((pos_and_pos_or_neg_and_neg_of_mul_pos h).resolve_left fun h => h.2.not_le ha).1
#align neg_of_mul_pos_left neg_of_mul_pos_left
-/

#print neg_iff_neg_of_mul_pos /-
theorem neg_iff_neg_of_mul_pos [PosMulMono α] [MulPosMono α] (hab : 0 < a * b) : a < 0 ↔ b < 0 :=
  ⟨neg_of_mul_pos_right hab ∘ le_of_lt, neg_of_mul_pos_left hab ∘ le_of_lt⟩
#align neg_iff_neg_of_mul_pos neg_iff_neg_of_mul_pos
-/

#print Left.neg_of_mul_neg_left /-
theorem Left.neg_of_mul_neg_left [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Left.mul_nonneg h1 h2).not_lt h
#align left.neg_of_mul_neg_left Left.neg_of_mul_neg_left
-/

#print Right.neg_of_mul_neg_left /-
theorem Right.neg_of_mul_neg_left [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ a) : b < 0 :=
  lt_of_not_ge fun h2 : b ≥ 0 => (Right.mul_nonneg h1 h2).not_lt h
#align right.neg_of_mul_neg_left Right.neg_of_mul_neg_left
-/

#print Left.neg_of_mul_neg_right /-
theorem Left.neg_of_mul_neg_right [PosMulMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Left.mul_nonneg h2 h1).not_lt h
#align left.neg_of_mul_neg_right Left.neg_of_mul_neg_right
-/

#print Right.neg_of_mul_neg_right /-
theorem Right.neg_of_mul_neg_right [MulPosMono α] (h : a * b < 0) (h1 : 0 ≤ b) : a < 0 :=
  lt_of_not_ge fun h2 : a ≥ 0 => (Right.mul_nonneg h2 h1).not_lt h
#align right.neg_of_mul_neg_right Right.neg_of_mul_neg_right
-/

end LinearOrder

end MulZeroClass

section MulOneClass

variable [MulOneClass α] [Zero α]

section Preorder

variable [Preorder α]

/-! Lemmas of the form `a ≤ a * b ↔ 1 ≤ b` and `a * b ≤ a ↔ b ≤ 1`,
which assume left covariance. -/


#print le_mul_iff_one_le_right /-
@[simp]
theorem le_mul_iff_one_le_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) :
    a ≤ a * b ↔ 1 ≤ b :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align le_mul_iff_one_le_right le_mul_iff_one_le_right
-/

#print lt_mul_iff_one_lt_right /-
@[simp]
theorem lt_mul_iff_one_lt_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a < a * b ↔ 1 < b :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align lt_mul_iff_one_lt_right lt_mul_iff_one_lt_right
-/

#print mul_le_iff_le_one_right /-
@[simp]
theorem mul_le_iff_le_one_right [PosMulMono α] [PosMulReflectLE α] (a0 : 0 < a) :
    a * b ≤ a ↔ b ≤ 1 :=
  Iff.trans (by rw [mul_one]) (mul_le_mul_left a0)
#align mul_le_iff_le_one_right mul_le_iff_le_one_right
-/

#print mul_lt_iff_lt_one_right /-
@[simp]
theorem mul_lt_iff_lt_one_right [PosMulStrictMono α] [PosMulReflectLT α] (a0 : 0 < a) :
    a * b < a ↔ b < 1 :=
  Iff.trans (by rw [mul_one]) (mul_lt_mul_left a0)
#align mul_lt_iff_lt_one_right mul_lt_iff_lt_one_right
-/

/-! Lemmas of the form `a ≤ b * a ↔ 1 ≤ b` and `a * b ≤ b ↔ a ≤ 1`,
which assume right covariance. -/


#print le_mul_iff_one_le_left /-
@[simp]
theorem le_mul_iff_one_le_left [MulPosMono α] [MulPosReflectLE α] (a0 : 0 < a) :
    a ≤ b * a ↔ 1 ≤ b :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right a0)
#align le_mul_iff_one_le_left le_mul_iff_one_le_left
-/

#print lt_mul_iff_one_lt_left /-
@[simp]
theorem lt_mul_iff_one_lt_left [MulPosStrictMono α] [MulPosReflectLT α] (a0 : 0 < a) :
    a < b * a ↔ 1 < b :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right a0)
#align lt_mul_iff_one_lt_left lt_mul_iff_one_lt_left
-/

#print mul_le_iff_le_one_left /-
@[simp]
theorem mul_le_iff_le_one_left [MulPosMono α] [MulPosReflectLE α] (b0 : 0 < b) :
    a * b ≤ b ↔ a ≤ 1 :=
  Iff.trans (by rw [one_mul]) (mul_le_mul_right b0)
#align mul_le_iff_le_one_left mul_le_iff_le_one_left
-/

#print mul_lt_iff_lt_one_left /-
@[simp]
theorem mul_lt_iff_lt_one_left [MulPosStrictMono α] [MulPosReflectLT α] (b0 : 0 < b) :
    a * b < b ↔ a < 1 :=
  Iff.trans (by rw [one_mul]) (mul_lt_mul_right b0)
#align mul_lt_iff_lt_one_left mul_lt_iff_lt_one_left
-/

/-! Lemmas of the form `1 ≤ b → a ≤ a * b`.

Variants with `< 0` and `≤ 0` instead of `0 <` and `0 ≤` appear in `algebra/order/ring/defs` (which
imports this file) as they need additional results which are not yet available here. -/


#print mul_le_of_le_one_left /-
theorem mul_le_of_le_one_left [MulPosMono α] (hb : 0 ≤ b) (h : a ≤ 1) : a * b ≤ b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align mul_le_of_le_one_left mul_le_of_le_one_left
-/

#print le_mul_of_one_le_left /-
theorem le_mul_of_one_le_left [MulPosMono α] (hb : 0 ≤ b) (h : 1 ≤ a) : b ≤ a * b := by
  simpa only [one_mul] using mul_le_mul_of_nonneg_right h hb
#align le_mul_of_one_le_left le_mul_of_one_le_left
-/

#print mul_le_of_le_one_right /-
theorem mul_le_of_le_one_right [PosMulMono α] (ha : 0 ≤ a) (h : b ≤ 1) : a * b ≤ a := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align mul_le_of_le_one_right mul_le_of_le_one_right
-/

#print le_mul_of_one_le_right /-
theorem le_mul_of_one_le_right [PosMulMono α] (ha : 0 ≤ a) (h : 1 ≤ b) : a ≤ a * b := by
  simpa only [mul_one] using mul_le_mul_of_nonneg_left h ha
#align le_mul_of_one_le_right le_mul_of_one_le_right
-/

#print mul_lt_of_lt_one_left /-
theorem mul_lt_of_lt_one_left [MulPosStrictMono α] (hb : 0 < b) (h : a < 1) : a * b < b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align mul_lt_of_lt_one_left mul_lt_of_lt_one_left
-/

#print lt_mul_of_one_lt_left /-
theorem lt_mul_of_one_lt_left [MulPosStrictMono α] (hb : 0 < b) (h : 1 < a) : b < a * b := by
  simpa only [one_mul] using mul_lt_mul_of_pos_right h hb
#align lt_mul_of_one_lt_left lt_mul_of_one_lt_left
-/

#print mul_lt_of_lt_one_right /-
theorem mul_lt_of_lt_one_right [PosMulStrictMono α] (ha : 0 < a) (h : b < 1) : a * b < a := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align mul_lt_of_lt_one_right mul_lt_of_lt_one_right
-/

#print lt_mul_of_one_lt_right /-
theorem lt_mul_of_one_lt_right [PosMulStrictMono α] (ha : 0 < a) (h : 1 < b) : a < a * b := by
  simpa only [mul_one] using mul_lt_mul_of_pos_left h ha
#align lt_mul_of_one_lt_right lt_mul_of_one_lt_right
-/

/-! Lemmas of the form `b ≤ c → a ≤ 1 → b * a ≤ c`. -/


#print mul_le_of_le_of_le_one_of_nonneg /-
/- Yaël: What's the point of these lemmas? They just chain an existing lemma with an assumption in
all possible ways, thereby artificially inflating the API and making the truly relevant lemmas hard
to find -/
theorem mul_le_of_le_of_le_one_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a ≤ c :=
  (mul_le_of_le_one_right hb ha).trans h
#align mul_le_of_le_of_le_one_of_nonneg mul_le_of_le_of_le_one_of_nonneg
-/

#print mul_lt_of_le_of_lt_one_of_pos /-
theorem mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : a < 1) (b0 : 0 < b) :
    b * a < c :=
  (mul_lt_of_lt_one_right b0 ha).trans_le bc
#align mul_lt_of_le_of_lt_one_of_pos mul_lt_of_le_of_lt_one_of_pos
-/

#print mul_lt_of_lt_of_le_one_of_nonneg /-
theorem mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (h : b < c) (ha : a ≤ 1) (hb : 0 ≤ b) :
    b * a < c :=
  (mul_le_of_le_one_right hb ha).trans_lt h
#align mul_lt_of_lt_of_le_one_of_nonneg mul_lt_of_lt_of_le_one_of_nonneg
-/

#print Left.mul_le_one_of_le_of_le /-
/-- Assumes left covariance. -/
theorem Left.mul_le_one_of_le_of_le [PosMulMono α] (ha : a ≤ 1) (hb : b ≤ 1) (a0 : 0 ≤ a) :
    a * b ≤ 1 :=
  mul_le_of_le_of_le_one_of_nonneg ha hb a0
#align left.mul_le_one_of_le_of_le Left.mul_le_one_of_le_of_le
-/

#print Left.mul_lt_of_le_of_lt_one_of_pos /-
/-- Assumes left covariance. -/
theorem Left.mul_lt_of_le_of_lt_one_of_pos [PosMulStrictMono α] (ha : a ≤ 1) (hb : b < 1)
    (a0 : 0 < a) : a * b < 1 :=
  mul_lt_of_le_of_lt_one_of_pos ha hb a0
#align left.mul_lt_of_le_of_lt_one_of_pos Left.mul_lt_of_le_of_lt_one_of_pos
-/

#print Left.mul_lt_of_lt_of_le_one_of_nonneg /-
/-- Assumes left covariance. -/
theorem Left.mul_lt_of_lt_of_le_one_of_nonneg [PosMulMono α] (ha : a < 1) (hb : b ≤ 1)
    (a0 : 0 ≤ a) : a * b < 1 :=
  mul_lt_of_lt_of_le_one_of_nonneg ha hb a0
#align left.mul_lt_of_lt_of_le_one_of_nonneg Left.mul_lt_of_lt_of_le_one_of_nonneg
-/

#print mul_le_of_le_of_le_one' /-
theorem mul_le_of_le_of_le_one' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : a ≤ 1) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : b * a ≤ c :=
  (mul_le_mul_of_nonneg_right bc a0).trans <| mul_le_of_le_one_right c0 ha
#align mul_le_of_le_of_le_one' mul_le_of_le_of_le_one'
-/

#print mul_lt_of_lt_of_le_one' /-
theorem mul_lt_of_lt_of_le_one' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_le_one' mul_lt_of_lt_of_le_one'
-/

#print mul_lt_of_le_of_lt_one' /-
theorem mul_lt_of_le_of_lt_one' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : a < 1)
    (a0 : 0 ≤ a) (c0 : 0 < c) : b * a < c :=
  (mul_le_mul_of_nonneg_right bc a0).trans_lt <| mul_lt_of_lt_one_right c0 ha
#align mul_lt_of_le_of_lt_one' mul_lt_of_le_of_lt_one'
-/

#print mul_lt_of_lt_of_lt_one_of_pos /-
theorem mul_lt_of_lt_of_lt_one_of_pos [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : a ≤ 1)
    (a0 : 0 < a) (c0 : 0 ≤ c) : b * a < c :=
  (mul_lt_mul_of_pos_right bc a0).trans_le <| mul_le_of_le_one_right c0 ha
#align mul_lt_of_lt_of_lt_one_of_pos mul_lt_of_lt_of_lt_one_of_pos
-/

/-! Lemmas of the form `b ≤ c → 1 ≤ a → b ≤ c * a`. -/


#print le_mul_of_le_of_one_le_of_nonneg /-
theorem le_mul_of_le_of_one_le_of_nonneg [PosMulMono α] (h : b ≤ c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b ≤ c * a :=
  h.trans <| le_mul_of_one_le_right hc ha
#align le_mul_of_le_of_one_le_of_nonneg le_mul_of_le_of_one_le_of_nonneg
-/

#print lt_mul_of_le_of_one_lt_of_pos /-
theorem lt_mul_of_le_of_one_lt_of_pos [PosMulStrictMono α] (bc : b ≤ c) (ha : 1 < a) (c0 : 0 < c) :
    b < c * a :=
  bc.trans_lt <| lt_mul_of_one_lt_right c0 ha
#align lt_mul_of_le_of_one_lt_of_pos lt_mul_of_le_of_one_lt_of_pos
-/

#print lt_mul_of_lt_of_one_le_of_nonneg /-
theorem lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (h : b < c) (ha : 1 ≤ a) (hc : 0 ≤ c) :
    b < c * a :=
  h.trans_le <| le_mul_of_one_le_right hc ha
#align lt_mul_of_lt_of_one_le_of_nonneg lt_mul_of_lt_of_one_le_of_nonneg
-/

#print Left.one_le_mul_of_le_of_le /-
/-- Assumes left covariance. -/
theorem Left.one_le_mul_of_le_of_le [PosMulMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (a0 : 0 ≤ a) :
    1 ≤ a * b :=
  le_mul_of_le_of_one_le_of_nonneg ha hb a0
#align left.one_le_mul_of_le_of_le Left.one_le_mul_of_le_of_le
-/

#print Left.one_lt_mul_of_le_of_lt_of_pos /-
/-- Assumes left covariance. -/
theorem Left.one_lt_mul_of_le_of_lt_of_pos [PosMulStrictMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (a0 : 0 < a) : 1 < a * b :=
  lt_mul_of_le_of_one_lt_of_pos ha hb a0
#align left.one_lt_mul_of_le_of_lt_of_pos Left.one_lt_mul_of_le_of_lt_of_pos
-/

#print Left.lt_mul_of_lt_of_one_le_of_nonneg /-
/-- Assumes left covariance. -/
theorem Left.lt_mul_of_lt_of_one_le_of_nonneg [PosMulMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (a0 : 0 ≤ a) : 1 < a * b :=
  lt_mul_of_lt_of_one_le_of_nonneg ha hb a0
#align left.lt_mul_of_lt_of_one_le_of_nonneg Left.lt_mul_of_lt_of_one_le_of_nonneg
-/

#print le_mul_of_le_of_one_le' /-
theorem le_mul_of_le_of_one_le' [PosMulMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 ≤ a) (a0 : 0 ≤ a)
    (b0 : 0 ≤ b) : b ≤ c * a :=
  (le_mul_of_one_le_right b0 ha).trans <| mul_le_mul_of_nonneg_right bc a0
#align le_mul_of_le_of_one_le' le_mul_of_le_of_one_le'
-/

#print lt_mul_of_le_of_one_lt' /-
theorem lt_mul_of_le_of_one_lt' [PosMulStrictMono α] [MulPosMono α] (bc : b ≤ c) (ha : 1 < a)
    (a0 : 0 ≤ a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans_le <| mul_le_mul_of_nonneg_right bc a0
#align lt_mul_of_le_of_one_lt' lt_mul_of_le_of_one_lt'
-/

#print lt_mul_of_lt_of_one_le' /-
theorem lt_mul_of_lt_of_one_le' [PosMulMono α] [MulPosStrictMono α] (bc : b < c) (ha : 1 ≤ a)
    (a0 : 0 < a) (b0 : 0 ≤ b) : b < c * a :=
  (le_mul_of_one_le_right b0 ha).trans_lt <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_le' lt_mul_of_lt_of_one_le'
-/

#print lt_mul_of_lt_of_one_lt_of_pos /-
theorem lt_mul_of_lt_of_one_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (bc : b < c)
    (ha : 1 < a) (a0 : 0 < a) (b0 : 0 < b) : b < c * a :=
  (lt_mul_of_one_lt_right b0 ha).trans <| mul_lt_mul_of_pos_right bc a0
#align lt_mul_of_lt_of_one_lt_of_pos lt_mul_of_lt_of_one_lt_of_pos
-/

/-! Lemmas of the form `a ≤ 1 → b ≤ c → a * b ≤ c`. -/


#print mul_le_of_le_one_of_le_of_nonneg /-
theorem mul_le_of_le_one_of_le_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b ≤ c) (hb : 0 ≤ b) :
    a * b ≤ c :=
  (mul_le_of_le_one_left hb ha).trans h
#align mul_le_of_le_one_of_le_of_nonneg mul_le_of_le_one_of_le_of_nonneg
-/

#print mul_lt_of_lt_one_of_le_of_pos /-
theorem mul_lt_of_lt_one_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (h : b ≤ c) (hb : 0 < b) :
    a * b < c :=
  (mul_lt_of_lt_one_left hb ha).trans_le h
#align mul_lt_of_lt_one_of_le_of_pos mul_lt_of_lt_one_of_le_of_pos
-/

#print mul_lt_of_le_one_of_lt_of_nonneg /-
theorem mul_lt_of_le_one_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (h : b < c) (hb : 0 ≤ b) :
    a * b < c :=
  (mul_le_of_le_one_left hb ha).trans_lt h
#align mul_lt_of_le_one_of_lt_of_nonneg mul_lt_of_le_one_of_lt_of_nonneg
-/

#print Right.mul_lt_one_of_lt_of_le_of_pos /-
/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : a < 1) (hb : b ≤ 1)
    (b0 : 0 < b) : a * b < 1 :=
  mul_lt_of_lt_one_of_le_of_pos ha hb b0
#align right.mul_lt_one_of_lt_of_le_of_pos Right.mul_lt_one_of_lt_of_le_of_pos
-/

#print Right.mul_lt_one_of_le_of_lt_of_nonneg /-
/-- Assumes right covariance. -/
theorem Right.mul_lt_one_of_le_of_lt_of_nonneg [MulPosMono α] (ha : a ≤ 1) (hb : b < 1)
    (b0 : 0 ≤ b) : a * b < 1 :=
  mul_lt_of_le_one_of_lt_of_nonneg ha hb b0
#align right.mul_lt_one_of_le_of_lt_of_nonneg Right.mul_lt_one_of_le_of_lt_of_nonneg
-/

#print mul_lt_of_lt_one_of_lt_of_pos /-
theorem mul_lt_of_lt_one_of_lt_of_pos [PosMulStrictMono α] [MulPosStrictMono α] (ha : a < 1)
    (bc : b < c) (a0 : 0 < a) (c0 : 0 < c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_lt_of_pos mul_lt_of_lt_one_of_lt_of_pos
-/

#print Right.mul_le_one_of_le_of_le /-
/-- Assumes right covariance. -/
theorem Right.mul_le_one_of_le_of_le [MulPosMono α] (ha : a ≤ 1) (hb : b ≤ 1) (b0 : 0 ≤ b) :
    a * b ≤ 1 :=
  mul_le_of_le_one_of_le_of_nonneg ha hb b0
#align right.mul_le_one_of_le_of_le Right.mul_le_one_of_le_of_le
-/

#print mul_le_of_le_one_of_le' /-
theorem mul_le_of_le_one_of_le' [PosMulMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b ≤ c) (a0 : 0 ≤ a)
    (c0 : 0 ≤ c) : a * b ≤ c :=
  (mul_le_mul_of_nonneg_left bc a0).trans <| mul_le_of_le_one_left c0 ha
#align mul_le_of_le_one_of_le' mul_le_of_le_one_of_le'
-/

#print mul_lt_of_lt_one_of_le' /-
theorem mul_lt_of_lt_one_of_le' [PosMulMono α] [MulPosStrictMono α] (ha : a < 1) (bc : b ≤ c)
    (a0 : 0 ≤ a) (c0 : 0 < c) : a * b < c :=
  (mul_le_mul_of_nonneg_left bc a0).trans_lt <| mul_lt_of_lt_one_left c0 ha
#align mul_lt_of_lt_one_of_le' mul_lt_of_lt_one_of_le'
-/

#print mul_lt_of_le_one_of_lt' /-
theorem mul_lt_of_le_one_of_lt' [PosMulStrictMono α] [MulPosMono α] (ha : a ≤ 1) (bc : b < c)
    (a0 : 0 < a) (c0 : 0 ≤ c) : a * b < c :=
  (mul_lt_mul_of_pos_left bc a0).trans_le <| mul_le_of_le_one_left c0 ha
#align mul_lt_of_le_one_of_lt' mul_lt_of_le_one_of_lt'
-/

/-! Lemmas of the form `1 ≤ a → b ≤ c → b ≤ a * c`. -/


#print lt_mul_of_one_lt_of_le_of_pos /-
theorem lt_mul_of_one_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b ≤ c) (hc : 0 < c) :
    b < a * c :=
  h.trans_lt <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_le_of_pos lt_mul_of_one_lt_of_le_of_pos
-/

#print lt_mul_of_one_le_of_lt_of_nonneg /-
theorem lt_mul_of_one_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_le_of_lt_of_nonneg lt_mul_of_one_le_of_lt_of_nonneg
-/

#print lt_mul_of_one_lt_of_lt_of_pos /-
theorem lt_mul_of_one_lt_of_lt_of_pos [MulPosStrictMono α] (ha : 1 < a) (h : b < c) (hc : 0 < c) :
    b < a * c :=
  h.trans <| lt_mul_of_one_lt_left hc ha
#align lt_mul_of_one_lt_of_lt_of_pos lt_mul_of_one_lt_of_lt_of_pos
-/

#print Right.one_lt_mul_of_lt_of_le_of_pos /-
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_le_of_pos [MulPosStrictMono α] (ha : 1 < a) (hb : 1 ≤ b)
    (b0 : 0 < b) : 1 < a * b :=
  lt_mul_of_one_lt_of_le_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_le_of_pos Right.one_lt_mul_of_lt_of_le_of_pos
-/

#print Right.one_lt_mul_of_le_of_lt_of_nonneg /-
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_le_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (hb : 1 < b)
    (b0 : 0 ≤ b) : 1 < a * b :=
  lt_mul_of_one_le_of_lt_of_nonneg ha hb b0
#align right.one_lt_mul_of_le_of_lt_of_nonneg Right.one_lt_mul_of_le_of_lt_of_nonneg
-/

#print Right.one_lt_mul_of_lt_of_lt /-
/-- Assumes right covariance. -/
theorem Right.one_lt_mul_of_lt_of_lt [MulPosStrictMono α] (ha : 1 < a) (hb : 1 < b) (b0 : 0 < b) :
    1 < a * b :=
  lt_mul_of_one_lt_of_lt_of_pos ha hb b0
#align right.one_lt_mul_of_lt_of_lt Right.one_lt_mul_of_lt_of_lt
-/

#print lt_mul_of_one_lt_of_lt_of_nonneg /-
theorem lt_mul_of_one_lt_of_lt_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (h : b < c) (hc : 0 ≤ c) :
    b < a * c :=
  h.trans_le <| le_mul_of_one_le_left hc ha
#align lt_mul_of_one_lt_of_lt_of_nonneg lt_mul_of_one_lt_of_lt_of_nonneg
-/

#print lt_of_mul_lt_of_one_le_of_nonneg_left /-
theorem lt_of_mul_lt_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b < c) (hle : 1 ≤ b)
    (ha : 0 ≤ a) : a < c :=
  (le_mul_of_one_le_right ha hle).trans_lt h
#align lt_of_mul_lt_of_one_le_of_nonneg_left lt_of_mul_lt_of_one_le_of_nonneg_left
-/

#print lt_of_lt_mul_of_le_one_of_nonneg_left /-
theorem lt_of_lt_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a < b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a < b :=
  h.trans_le <| mul_le_of_le_one_right hb hc
#align lt_of_lt_mul_of_le_one_of_nonneg_left lt_of_lt_mul_of_le_one_of_nonneg_left
-/

#print lt_of_lt_mul_of_le_one_of_nonneg_right /-
theorem lt_of_lt_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a < b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a < c :=
  h.trans_le <| mul_le_of_le_one_left hc hb
#align lt_of_lt_mul_of_le_one_of_nonneg_right lt_of_lt_mul_of_le_one_of_nonneg_right
-/

#print le_mul_of_one_le_of_le_of_nonneg /-
theorem le_mul_of_one_le_of_le_of_nonneg [MulPosMono α] (ha : 1 ≤ a) (bc : b ≤ c) (c0 : 0 ≤ c) :
    b ≤ a * c :=
  bc.trans <| le_mul_of_one_le_left c0 ha
#align le_mul_of_one_le_of_le_of_nonneg le_mul_of_one_le_of_le_of_nonneg
-/

#print Right.one_le_mul_of_le_of_le /-
/-- Assumes right covariance. -/
theorem Right.one_le_mul_of_le_of_le [MulPosMono α] (ha : 1 ≤ a) (hb : 1 ≤ b) (b0 : 0 ≤ b) :
    1 ≤ a * b :=
  le_mul_of_one_le_of_le_of_nonneg ha hb b0
#align right.one_le_mul_of_le_of_le Right.one_le_mul_of_le_of_le
-/

#print le_of_mul_le_of_one_le_of_nonneg_left /-
theorem le_of_mul_le_of_one_le_of_nonneg_left [PosMulMono α] (h : a * b ≤ c) (hb : 1 ≤ b)
    (ha : 0 ≤ a) : a ≤ c :=
  (le_mul_of_one_le_right ha hb).trans h
#align le_of_mul_le_of_one_le_of_nonneg_left le_of_mul_le_of_one_le_of_nonneg_left
-/

#print le_of_le_mul_of_le_one_of_nonneg_left /-
theorem le_of_le_mul_of_le_one_of_nonneg_left [PosMulMono α] (h : a ≤ b * c) (hc : c ≤ 1)
    (hb : 0 ≤ b) : a ≤ b :=
  h.trans <| mul_le_of_le_one_right hb hc
#align le_of_le_mul_of_le_one_of_nonneg_left le_of_le_mul_of_le_one_of_nonneg_left
-/

#print le_of_mul_le_of_one_le_nonneg_right /-
theorem le_of_mul_le_of_one_le_nonneg_right [MulPosMono α] (h : a * b ≤ c) (ha : 1 ≤ a)
    (hb : 0 ≤ b) : b ≤ c :=
  (le_mul_of_one_le_left hb ha).trans h
#align le_of_mul_le_of_one_le_nonneg_right le_of_mul_le_of_one_le_nonneg_right
-/

#print le_of_le_mul_of_le_one_of_nonneg_right /-
theorem le_of_le_mul_of_le_one_of_nonneg_right [MulPosMono α] (h : a ≤ b * c) (hb : b ≤ 1)
    (hc : 0 ≤ c) : a ≤ c :=
  h.trans <| mul_le_of_le_one_left hc hb
#align le_of_le_mul_of_le_one_of_nonneg_right le_of_le_mul_of_le_one_of_nonneg_right
-/

end Preorder

section LinearOrder

variable [LinearOrder α]

#print exists_square_le' /-
-- Yaël: What's the point of this lemma? If we have `0 * 0 = 0`, then we can just take `b = 0`.
-- proven with `a0 : 0 ≤ a` as `exists_square_le`
theorem exists_square_le' [PosMulStrictMono α] (a0 : 0 < a) : ∃ b : α, b * b ≤ a :=
  by
  obtain ha | ha := lt_or_le a 1
  · exact ⟨a, (mul_lt_of_lt_one_right a0 ha).le⟩
  · exact ⟨1, by rwa [mul_one]⟩
#align exists_square_le' exists_square_le'
-/

end LinearOrder

end MulOneClass

section CancelMonoidWithZero

variable [CancelMonoidWithZero α]

section PartialOrder

variable [PartialOrder α]

#print PosMulMono.toPosMulStrictMono /-
theorem PosMulMono.toPosMulStrictMono [PosMulMono α] : PosMulStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_left h.le x.2.le).lt_of_ne (h.Ne ∘ mul_left_cancel₀ x.2.ne')⟩
#align pos_mul_mono.to_pos_mul_strict_mono PosMulMono.toPosMulStrictMono
-/

#print posMulMono_iff_posMulStrictMono /-
theorem posMulMono_iff_posMulStrictMono : PosMulMono α ↔ PosMulStrictMono α :=
  ⟨@PosMulMono.toPosMulStrictMono α _ _, @PosMulStrictMono.toPosMulMono α _ _⟩
#align pos_mul_mono_iff_pos_mul_strict_mono posMulMono_iff_posMulStrictMono
-/

#print MulPosMono.toMulPosStrictMono /-
theorem MulPosMono.toMulPosStrictMono [MulPosMono α] : MulPosStrictMono α :=
  ⟨fun x a b h =>
    (mul_le_mul_of_nonneg_right h.le x.2.le).lt_of_ne (h.Ne ∘ mul_right_cancel₀ x.2.ne')⟩
#align mul_pos_mono.to_mul_pos_strict_mono MulPosMono.toMulPosStrictMono
-/

#print mulPosMono_iff_mulPosStrictMono /-
theorem mulPosMono_iff_mulPosStrictMono : MulPosMono α ↔ MulPosStrictMono α :=
  ⟨@MulPosMono.toMulPosStrictMono α _ _, @MulPosStrictMono.toMulPosMono α _ _⟩
#align mul_pos_mono_iff_mul_pos_strict_mono mulPosMono_iff_mulPosStrictMono
-/

#print PosMulReflectLT.toPosMulReflectLE /-
theorem PosMulReflectLT.toPosMulReflectLE [PosMulReflectLT α] : PosMulReflectLE α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_left_cancel₀ x.2.Ne.symm) fun h' =>
      (lt_of_mul_lt_mul_left h' x.2.le).le⟩
#align pos_mul_reflect_lt.to_pos_mul_mono_rev PosMulReflectLT.toPosMulReflectLE
-/

#print posMulReflectLE_iff_posMulReflectLT /-
theorem posMulReflectLE_iff_posMulReflectLT : PosMulReflectLE α ↔ PosMulReflectLT α :=
  ⟨@PosMulReflectLE.toPosMulReflectLT α _ _, @PosMulReflectLT.toPosMulReflectLE α _ _⟩
#align pos_mul_mono_rev_iff_pos_mul_reflect_lt posMulReflectLE_iff_posMulReflectLT
-/

#print MulPosReflectLT.toMulPosReflectLE /-
theorem MulPosReflectLT.toMulPosReflectLE [MulPosReflectLT α] : MulPosReflectLE α :=
  ⟨fun x a b h =>
    h.eq_or_lt.elim (le_of_eq ∘ mul_right_cancel₀ x.2.Ne.symm) fun h' =>
      (lt_of_mul_lt_mul_right h' x.2.le).le⟩
#align mul_pos_reflect_lt.to_mul_pos_mono_rev MulPosReflectLT.toMulPosReflectLE
-/

#print mulPosReflectLE_iff_mulPosReflectLT /-
theorem mulPosReflectLE_iff_mulPosReflectLT : MulPosReflectLE α ↔ MulPosReflectLT α :=
  ⟨@MulPosReflectLE.toMulPosReflectLT α _ _, @MulPosReflectLT.toMulPosReflectLE α _ _⟩
#align mul_pos_mono_rev_iff_mul_pos_reflect_lt mulPosReflectLE_iff_mulPosReflectLT
-/

end PartialOrder

end CancelMonoidWithZero

section CommSemigroupHasZero

variable [CommSemigroup α] [Zero α] [Preorder α]

#print posMulStrictMono_iff_mulPosStrictMono /-
theorem posMulStrictMono_iff_mulPosStrictMono : PosMulStrictMono α ↔ MulPosStrictMono α := by
  simp! only [mul_comm]
#align pos_mul_strict_mono_iff_mul_pos_strict_mono posMulStrictMono_iff_mulPosStrictMono
-/

#print posMulReflectLT_iff_mulPosReflectLT /-
theorem posMulReflectLT_iff_mulPosReflectLT : PosMulReflectLT α ↔ MulPosReflectLT α := by
  simp! only [mul_comm]
#align pos_mul_reflect_lt_iff_mul_pos_reflect_lt posMulReflectLT_iff_mulPosReflectLT
-/

#print posMulMono_iff_mulPosMono /-
theorem posMulMono_iff_mulPosMono : PosMulMono α ↔ MulPosMono α := by simp! only [mul_comm]
#align pos_mul_mono_iff_mul_pos_mono posMulMono_iff_mulPosMono
-/

#print posMulReflectLE_iff_mulPosReflectLE /-
theorem posMulReflectLE_iff_mulPosReflectLE : PosMulReflectLE α ↔ MulPosReflectLE α := by
  simp! only [mul_comm]
#align pos_mul_mono_rev_iff_mul_pos_mono_rev posMulReflectLE_iff_mulPosReflectLE
-/

end CommSemigroupHasZero

