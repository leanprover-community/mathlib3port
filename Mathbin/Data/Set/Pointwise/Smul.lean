/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn

! This file was ported from Lean 3 source module data.set.pointwise.smul
! leanprover-community/mathlib commit 5e526d18cea33550268dcbbddcb822d5cde40654
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Module.Basic
import Mathbin.Data.Set.Pairwise.Lattice
import Mathbin.Data.Set.Pointwise.Basic
import Mathbin.Tactic.ByContra

/-!
# Pointwise operations of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

-/


open Function MulOpposite

variable {F α β γ : Type _}

namespace Set

open Pointwise

/-! ### Translation/scaling of sets -/


section Smul

#print Set.smulSet /-
/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive
      "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in\nlocale `pointwise`."]
protected def smulSet [SMul α β] : SMul α (Set β) :=
  ⟨fun a => image (SMul.smul a)⟩
#align set.has_smul_set Set.smulSet
#align set.has_vadd_set Set.vaddSet
-/

#print Set.smul /-
/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive
      "The pointwise scalar addition of sets `s +ᵥ t` is defined as\n`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def smul [SMul α β] : SMul (Set α) (Set β) :=
  ⟨image2 SMul.smul⟩
#align set.has_smul Set.smul
#align set.has_vadd Set.vadd
-/

scoped[Pointwise] attribute [instance] Set.smulSet Set.smul

scoped[Pointwise] attribute [instance] Set.vaddSet Set.vadd

section SMul

variable {ι : Sort _} {κ : ι → Sort _} [SMul α β] {s s₁ s₂ : Set α} {t t₁ t₂ u : Set β} {a : α}
  {b : β}

#print Set.image2_smul /-
@[simp, to_additive]
theorem image2_smul : image2 SMul.smul s t = s • t :=
  rfl
#align set.image2_smul Set.image2_smul
#align set.image2_vadd Set.image2_vadd
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Set.image_smul_prod /-
@[to_additive add_image_prod]
theorem image_smul_prod : (fun x : α × β => x.fst • x.snd) '' s ×ˢ t = s • t :=
  image_prod _
#align set.image_smul_prod Set.image_smul_prod
#align set.add_image_prod Set.add_image_prod
-/

#print Set.mem_smul /-
@[to_additive]
theorem mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b :=
  Iff.rfl
#align set.mem_smul Set.mem_smul
#align set.mem_vadd Set.mem_vadd
-/

/- warning: set.smul_mem_smul -> Set.smul_mem_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t : Set.{u2} β} {a : α} {b : β}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) b t) -> (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β _inst_1 a b) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] {s : Set.{u2} α} {t : Set.{u1} β} {a : α} {b : β}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) b t) -> (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) a b) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s t))
Case conversion may be inaccurate. Consider using '#align set.smul_mem_smul Set.smul_mem_smulₓ'. -/
@[to_additive]
theorem smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t :=
  mem_image2_of_mem
#align set.smul_mem_smul Set.smul_mem_smul
#align set.vadd_mem_vadd Set.vadd_mem_vadd

#print Set.empty_smul /-
@[simp, to_additive]
theorem empty_smul : (∅ : Set α) • t = ∅ :=
  image2_empty_left
#align set.empty_smul Set.empty_smul
#align set.empty_vadd Set.empty_vadd
-/

#print Set.smul_empty /-
@[simp, to_additive]
theorem smul_empty : s • (∅ : Set β) = ∅ :=
  image2_empty_right
#align set.smul_empty Set.smul_empty
#align set.vadd_empty Set.vadd_empty
-/

#print Set.smul_eq_empty /-
@[simp, to_additive]
theorem smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.smul_eq_empty Set.smul_eq_empty
#align set.vadd_eq_empty Set.vadd_eq_empty
-/

#print Set.smul_nonempty /-
@[simp, to_additive]
theorem smul_nonempty : (s • t).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.smul_nonempty Set.smul_nonempty
#align set.vadd_nonempty Set.vadd_nonempty
-/

/- warning: set.nonempty.smul -> Set.Nonempty.smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t : Set.{u2} β}, (Set.Nonempty.{u1} α s) -> (Set.Nonempty.{u2} β t) -> (Set.Nonempty.{u2} β (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] {s : Set.{u2} α} {t : Set.{u1} β}, (Set.Nonempty.{u2} α s) -> (Set.Nonempty.{u1} β t) -> (Set.Nonempty.{u1} β (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s t))
Case conversion may be inaccurate. Consider using '#align set.nonempty.smul Set.Nonempty.smulₓ'. -/
@[to_additive]
theorem Nonempty.smul : s.Nonempty → t.Nonempty → (s • t).Nonempty :=
  Nonempty.image2
#align set.nonempty.smul Set.Nonempty.smul
#align set.nonempty.vadd Set.Nonempty.vadd

#print Set.Nonempty.of_smul_left /-
@[to_additive]
theorem Nonempty.of_smul_left : (s • t).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_smul_left Set.Nonempty.of_smul_left
#align set.nonempty.of_vadd_left Set.Nonempty.of_vadd_left
-/

#print Set.Nonempty.of_smul_right /-
@[to_additive]
theorem Nonempty.of_smul_right : (s • t).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_smul_right Set.Nonempty.of_smul_right
#align set.nonempty.of_vadd_right Set.Nonempty.of_vadd_right
-/

#print Set.smul_singleton /-
@[simp, to_additive]
theorem smul_singleton : s • {b} = (· • b) '' s :=
  image2_singleton_right
#align set.smul_singleton Set.smul_singleton
#align set.vadd_singleton Set.vadd_singleton
-/

#print Set.singleton_smul /-
@[simp, to_additive]
theorem singleton_smul : ({a} : Set α) • t = a • t :=
  image2_singleton_left
#align set.singleton_smul Set.singleton_smul
#align set.singleton_vadd Set.singleton_vadd
-/

#print Set.singleton_smul_singleton /-
@[simp, to_additive]
theorem singleton_smul_singleton : ({a} : Set α) • ({b} : Set β) = {a • b} :=
  image2_singleton
#align set.singleton_smul_singleton Set.singleton_smul_singleton
#align set.singleton_vadd_singleton Set.singleton_vadd_singleton
-/

/- warning: set.smul_subset_smul -> Set.smul_subset_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) t₁ t₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t₁) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) t₁ t₂) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s₁ t₁) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.smul_subset_smul Set.smul_subset_smulₓ'. -/
@[to_additive, mono]
theorem smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ :=
  image2_subset
#align set.smul_subset_smul Set.smul_subset_smul
#align set.vadd_subset_vadd Set.vadd_subset_vadd

#print Set.smul_subset_smul_left /-
@[to_additive]
theorem smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ :=
  image2_subset_left
#align set.smul_subset_smul_left Set.smul_subset_smul_left
#align set.vadd_subset_vadd_left Set.vadd_subset_vadd_left
-/

/- warning: set.smul_subset_smul_right -> Set.smul_subset_smul_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s₁ s₂) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] {s₁ : Set.{u2} α} {s₂ : Set.{u2} α} {t : Set.{u1} β}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s₁ s₂) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s₁ t) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.smul_subset_smul_right Set.smul_subset_smul_rightₓ'. -/
@[to_additive]
theorem smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t :=
  image2_subset_right
#align set.smul_subset_smul_right Set.smul_subset_smul_right
#align set.vadd_subset_vadd_right Set.vadd_subset_vadd_right

#print Set.smul_subset_iff /-
@[to_additive]
theorem smul_subset_iff : s • t ⊆ u ↔ ∀ a ∈ s, ∀ b ∈ t, a • b ∈ u :=
  image2_subset_iff
#align set.smul_subset_iff Set.smul_subset_iff
#align set.vadd_subset_iff Set.vadd_subset_iff
-/

attribute [mono] vadd_subset_vadd

/- warning: set.union_smul -> Set.union_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) t) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) t) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₁ t) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_smul Set.union_smulₓ'. -/
@[to_additive]
theorem union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
  image2_union_left
#align set.union_smul Set.union_smul
#align set.union_vadd Set.union_vadd

/- warning: set.smul_union -> Set.smul_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t₁) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s t₁) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.smul_union Set.smul_unionₓ'. -/
@[to_additive]
theorem smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ :=
  image2_union_right
#align set.smul_union Set.smul_union
#align set.vadd_union Set.vadd_union

/- warning: set.inter_smul_subset -> Set.inter_smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) t) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) t) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₁ t) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.inter_smul_subset Set.inter_smul_subsetₓ'. -/
@[to_additive]
theorem inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
  image2_inter_subset_left
#align set.inter_smul_subset Set.inter_smul_subset
#align set.inter_vadd_subset Set.inter_vadd_subset

/- warning: set.smul_inter_subset -> Set.smul_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t₁) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s t₁) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s t₂))
Case conversion may be inaccurate. Consider using '#align set.smul_inter_subset Set.smul_inter_subsetₓ'. -/
@[to_additive]
theorem smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
  image2_inter_subset_right
#align set.smul_inter_subset Set.smul_inter_subset
#align set.vadd_inter_subset Set.vadd_inter_subset

/- warning: set.inter_smul_union_subset_union -> Set.inter_smul_union_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t₁) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₁ t₁) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.inter_smul_union_subset_union Set.inter_smul_union_subset_unionₓ'. -/
@[to_additive]
theorem inter_smul_union_subset_union : (s₁ ∩ s₂) • (t₁ ∪ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_inter_union_subset_union
#align set.inter_smul_union_subset_union Set.inter_smul_union_subset_union
#align set.inter_vadd_union_subset_union Set.inter_vadd_union_subset_union

/- warning: set.union_smul_inter_subset_union -> Set.union_smul_inter_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₁ t₁) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s₂ t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {s₁ : Set.{u1} α} {s₂ : Set.{u1} α} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₁ t₁) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1)) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.union_smul_inter_subset_union Set.union_smul_inter_subset_unionₓ'. -/
@[to_additive]
theorem union_smul_inter_subset_union : (s₁ ∪ s₂) • (t₁ ∩ t₂) ⊆ s₁ • t₁ ∪ s₂ • t₂ :=
  image2_union_inter_subset_union
#align set.union_smul_inter_subset_union Set.union_smul_inter_subset_union
#align set.union_vadd_inter_subset_union Set.union_vadd_inter_subset_union

#print Set.unionᵢ_smul_left_image /-
@[to_additive]
theorem unionᵢ_smul_left_image : (⋃ a ∈ s, a • t) = s • t :=
  unionᵢ_image_left _
#align set.Union_smul_left_image Set.unionᵢ_smul_left_image
#align set.Union_vadd_left_image Set.unionᵢ_vadd_left_image
-/

#print Set.unionᵢ_smul_right_image /-
@[to_additive]
theorem unionᵢ_smul_right_image : (⋃ a ∈ t, (· • a) '' s) = s • t :=
  unionᵢ_image_right _
#align set.Union_smul_right_image Set.unionᵢ_smul_right_image
#align set.Union_vadd_right_image Set.unionᵢ_vadd_right_image
-/

/- warning: set.Union_smul -> Set.unionᵢ_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (s : ι -> (Set.{u1} α)) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (s i) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SMul.{u3, u2} α β] (s : ι -> (Set.{u3} α)) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) (Set.unionᵢ.{u3, u1} α ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Union_smul Set.unionᵢ_smulₓ'. -/
@[to_additive]
theorem unionᵢ_smul (s : ι → Set α) (t : Set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
  image2_unionᵢ_left _ _ _
#align set.Union_smul Set.unionᵢ_smul
#align set.Union_vadd Set.unionᵢ_vadd

/- warning: set.smul_Union -> Set.smul_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (s : Set.{u1} α) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SMul.{u3, u2} α β] (s : Set.{u3} α) (t : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) s (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} β ι (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.smul_Union Set.smul_unionᵢₓ'. -/
@[to_additive]
theorem smul_unionᵢ (s : Set α) (t : ι → Set β) : (s • ⋃ i, t i) = ⋃ i, s • t i :=
  image2_unionᵢ_right _ _ _
#align set.smul_Union Set.smul_unionᵢ
#align set.vadd_Union Set.vadd_unionᵢ

/- warning: set.Union₂_smul -> Set.unionᵢ₂_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (s i j) t)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u4, u3} α β] (s : forall (i : ι), (κ i) -> (Set.{u4} α)) (t : Set.{u3} β), Eq.{succ u3} (Set.{u3} β) (HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) (Set.unionᵢ.{u4, u2} α ι (fun (i : ι) => Set.unionᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_smul Set.unionᵢ₂_smulₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem unionᵢ₂_smul (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋃ (i) (j), s i j) • t = ⋃ (i) (j), s i j • t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_smul Set.unionᵢ₂_smul
#align set.Union₂_vadd Set.unionᵢ₂_vadd

/- warning: set.smul_Union₂ -> Set.smul_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u4, u3} α β] (s : Set.{u4} α) (t : forall (i : ι), (κ i) -> (Set.{u3} β)), Eq.{succ u3} (Set.{u3} β) (HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) s (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} β ι (fun (i : ι) => Set.unionᵢ.{u3, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.smul_Union₂ Set.smul_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_unionᵢ₂ (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋃ (i) (j), t i j) = ⋃ (i) (j), s • t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.smul_Union₂ Set.smul_unionᵢ₂
#align set.vadd_Union₂ Set.vadd_unionᵢ₂

/- warning: set.Inter_smul_subset -> Set.interᵢ_smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (s : ι -> (Set.{u1} α)) (t : Set.{u2} β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (s i) t))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SMul.{u3, u2} α β] (s : ι -> (Set.{u3} α)) (t : Set.{u2} β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) (Set.interᵢ.{u3, u1} α ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Inter_smul_subset Set.interᵢ_smul_subsetₓ'. -/
@[to_additive]
theorem interᵢ_smul_subset (s : ι → Set α) (t : Set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_smul_subset Set.interᵢ_smul_subset
#align set.Inter_vadd_subset Set.interᵢ_vadd_subset

/- warning: set.smul_Inter_subset -> Set.smul_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (s : Set.{u1} α) (t : ι -> (Set.{u2} β)), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (t i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {ι : Sort.{u1}} [_inst_1 : SMul.{u3, u2} α β] (s : Set.{u3} α) (t : ι -> (Set.{u2} β)), HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) s (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} β ι (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} (Set.{u3} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} (Set.{u3} α) (Set.{u2} β) (Set.smul.{u3, u2} α β _inst_1)) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.smul_Inter_subset Set.smul_interᵢ_subsetₓ'. -/
@[to_additive]
theorem smul_interᵢ_subset (s : Set α) (t : ι → Set β) : (s • ⋂ i, t i) ⊆ ⋂ i, s • t i :=
  image2_interᵢ_subset_right _ _ _
#align set.smul_Inter_subset Set.smul_interᵢ_subset
#align set.vadd_Inter_subset Set.vadd_interᵢ_subset

/- warning: set.Inter₂_smul_subset -> Set.interᵢ₂_smul_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (s : forall (i : ι), (κ i) -> (Set.{u1} α)) (t : Set.{u2} β), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (s i j) t)))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u4, u3} α β] (s : forall (i : ι), (κ i) -> (Set.{u4} α)) (t : Set.{u3} β), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) (Set.interᵢ.{u4, u2} α ι (fun (i : ι) => Set.interᵢ.{u4, u1} α (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_smul_subset Set.interᵢ₂_smul_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem interᵢ₂_smul_subset (s : ∀ i, κ i → Set α) (t : Set β) :
    (⋂ (i) (j), s i j) • t ⊆ ⋂ (i) (j), s i j • t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_smul_subset Set.interᵢ₂_smul_subset
#align set.Inter₂_vadd_subset Set.interᵢ₂_vadd_subset

/- warning: set.smul_Inter₂_subset -> Set.smul_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (s : Set.{u1} α) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s (t i j))))
but is expected to have type
  forall {α : Type.{u4}} {β : Type.{u3}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u4, u3} α β] (s : Set.{u4} α) (t : forall (i : ι), (κ i) -> (Set.{u3} β)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) s (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} β ι (fun (i : ι) => Set.interᵢ.{u3, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u4, u3, u3} (Set.{u4} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u4, u3} (Set.{u4} α) (Set.{u3} β) (Set.smul.{u4, u3} α β _inst_1)) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.smul_Inter₂_subset Set.smul_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_interᵢ₂_subset (s : Set α) (t : ∀ i, κ i → Set β) :
    (s • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s • t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.smul_Inter₂_subset Set.smul_interᵢ₂_subset
#align set.vadd_Inter₂_subset Set.vadd_interᵢ₂_subset

/- warning: set.smul_set_subset_smul -> Set.smul_set_subset_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {t : Set.{u2} β} {a : α} {s : Set.{u1} α}, (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) -> (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] {t : Set.{u1} β} {a : α} {s : Set.{u2} α}, (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) -> (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β _inst_1)) a t) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s t))
Case conversion may be inaccurate. Consider using '#align set.smul_set_subset_smul Set.smul_set_subset_smulₓ'. -/
@[to_additive]
theorem smul_set_subset_smul {s : Set α} : a ∈ s → a • t ⊆ s • t :=
  image_subset_image2_right
#align set.smul_set_subset_smul Set.smul_set_subset_smul
#align set.vadd_set_subset_vadd Set.vadd_set_subset_vadd

/- warning: set.bUnion_smul_set -> Set.unionᵢ_smul_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (a : α) => Set.unionᵢ.{u2, 0} β (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t))) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : SMul.{u2, u1} α β] (s : Set.{u2} α) (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.unionᵢ.{u1, succ u2} β α (fun (a : α) => Set.unionᵢ.{u1, 0} β (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) (fun (H : Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a s) => HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β _inst_1)) a t))) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) s t)
Case conversion may be inaccurate. Consider using '#align set.bUnion_smul_set Set.unionᵢ_smul_setₓ'. -/
@[simp, to_additive]
theorem unionᵢ_smul_set (s : Set α) (t : Set β) : (⋃ a ∈ s, a • t) = s • t :=
  unionᵢ_image_left _
#align set.bUnion_smul_set Set.unionᵢ_smul_set
#align set.bUnion_vadd_set Set.unionᵢ_vadd_set

end SMul

section HasSmulSet

variable {ι : Sort _} {κ : ι → Sort _} [SMul α β] {s t t₁ t₂ : Set β} {a : α} {b : β} {x y : β}

#print Set.image_smul /-
@[simp, to_additive]
theorem image_smul : (fun x => a • x) '' t = a • t :=
  rfl
#align set.image_smul Set.image_smul
#align set.image_vadd Set.image_vadd
-/

#print Set.mem_smul_set /-
@[to_additive]
theorem mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x :=
  Iff.rfl
#align set.mem_smul_set Set.mem_smul_set
#align set.mem_vadd_set Set.mem_vadd_set
-/

#print Set.smul_mem_smul_set /-
@[to_additive]
theorem smul_mem_smul_set : b ∈ s → a • b ∈ a • s :=
  mem_image_of_mem _
#align set.smul_mem_smul_set Set.smul_mem_smul_set
#align set.vadd_mem_vadd_set Set.vadd_mem_vadd_set
-/

#print Set.smul_set_empty /-
@[simp, to_additive]
theorem smul_set_empty : a • (∅ : Set β) = ∅ :=
  image_empty _
#align set.smul_set_empty Set.smul_set_empty
#align set.vadd_set_empty Set.vadd_set_empty
-/

#print Set.smul_set_eq_empty /-
@[simp, to_additive]
theorem smul_set_eq_empty : a • s = ∅ ↔ s = ∅ :=
  image_eq_empty
#align set.smul_set_eq_empty Set.smul_set_eq_empty
#align set.vadd_set_eq_empty Set.vadd_set_eq_empty
-/

#print Set.smul_set_nonempty /-
@[simp, to_additive]
theorem smul_set_nonempty : (a • s).Nonempty ↔ s.Nonempty :=
  nonempty_image_iff
#align set.smul_set_nonempty Set.smul_set_nonempty
#align set.vadd_set_nonempty Set.vadd_set_nonempty
-/

#print Set.smul_set_singleton /-
@[simp, to_additive]
theorem smul_set_singleton : a • ({b} : Set β) = {a • b} :=
  image_singleton
#align set.smul_set_singleton Set.smul_set_singleton
#align set.vadd_set_singleton Set.vadd_set_singleton
-/

#print Set.smul_set_mono /-
@[to_additive]
theorem smul_set_mono : s ⊆ t → a • s ⊆ a • t :=
  image_subset _
#align set.smul_set_mono Set.smul_set_mono
#align set.vadd_set_mono Set.vadd_set_mono
-/

#print Set.smul_set_subset_iff /-
@[to_additive]
theorem smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t :=
  image_subset_iff
#align set.smul_set_subset_iff Set.smul_set_subset_iff
#align set.vadd_set_subset_iff Set.vadd_set_subset_iff
-/

/- warning: set.smul_set_union -> Set.smul_set_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t₁) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} β) (Set.instUnionSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a t₁) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a t₂))
Case conversion may be inaccurate. Consider using '#align set.smul_set_union Set.smul_set_unionₓ'. -/
@[to_additive]
theorem smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ :=
  image_union _ _ _
#align set.smul_set_union Set.smul_set_union
#align set.vadd_set_union Set.vadd_set_union

/- warning: set.smul_set_inter_subset -> Set.smul_set_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {a : α}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t₁) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a t₂))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : SMul.{u1, u2} α β] {t₁ : Set.{u2} β} {t₂ : Set.{u2} β} {a : α}, HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a t₁) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1)) a t₂))
Case conversion may be inaccurate. Consider using '#align set.smul_set_inter_subset Set.smul_set_inter_subsetₓ'. -/
@[to_additive]
theorem smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ a • t₂ :=
  image_inter_subset _ _ _
#align set.smul_set_inter_subset Set.smul_set_inter_subset
#align set.vadd_set_inter_subset Set.vadd_set_inter_subset

/- warning: set.smul_set_Union -> Set.smul_set_Union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (s : ι -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (s i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : SMul.{u2, u3} α β] (a : α) (s : ι -> (Set.{u3} β)), Eq.{succ u3} (Set.{u3} β) (HSMul.hSMul.{u2, u3, u3} α (Set.{u3} β) (Set.{u3} β) (instHSMul.{u2, u3} α (Set.{u3} β) (Set.smulSet.{u2, u3} α β _inst_1)) a (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => s i))) (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => HSMul.hSMul.{u2, u3, u3} α (Set.{u3} β) (Set.{u3} β) (instHSMul.{u2, u3} α (Set.{u3} β) (Set.smulSet.{u2, u3} α β _inst_1)) a (s i)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_Union Set.smul_set_Unionₓ'. -/
@[to_additive]
theorem smul_set_Union (a : α) (s : ι → Set β) : (a • ⋃ i, s i) = ⋃ i, a • s i :=
  image_unionᵢ
#align set.smul_set_Union Set.smul_set_Union
#align set.vadd_set_Union Set.vadd_set_Union

/- warning: set.smul_set_Union₂ -> Set.smul_set_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (s : forall (i : ι), (κ i) -> (Set.{u2} β)), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (s i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u3, u4} α β] (a : α) (s : forall (i : ι), (κ i) -> (Set.{u4} β)), Eq.{succ u4} (Set.{u4} β) (HSMul.hSMul.{u3, u4, u4} α (Set.{u4} β) (Set.{u4} β) (instHSMul.{u3, u4} α (Set.{u4} β) (Set.smulSet.{u3, u4} α β _inst_1)) a (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => s i j)))) (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u3, u4, u4} α (Set.{u4} β) (Set.{u4} β) (instHSMul.{u3, u4} α (Set.{u4} β) (Set.smulSet.{u3, u4} α β _inst_1)) a (s i j))))
Case conversion may be inaccurate. Consider using '#align set.smul_set_Union₂ Set.smul_set_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_unionᵢ₂ (a : α) (s : ∀ i, κ i → Set β) :
    (a • ⋃ (i) (j), s i j) = ⋃ (i) (j), a • s i j :=
  image_unionᵢ₂ _ _
#align set.smul_set_Union₂ Set.smul_set_unionᵢ₂
#align set.vadd_set_Union₂ Set.vadd_set_unionᵢ₂

/- warning: set.smul_set_Inter_subset -> Set.smul_set_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (t : ι -> (Set.{u2} β)), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : SMul.{u2, u3} α β] (a : α) (t : ι -> (Set.{u3} β)), HasSubset.Subset.{u3} (Set.{u3} β) (Set.instHasSubsetSet.{u3} β) (HSMul.hSMul.{u2, u3, u3} α (Set.{u3} β) (Set.{u3} β) (instHSMul.{u2, u3} α (Set.{u3} β) (Set.smulSet.{u2, u3} α β _inst_1)) a (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => HSMul.hSMul.{u2, u3, u3} α (Set.{u3} β) (Set.{u3} β) (instHSMul.{u2, u3} α (Set.{u3} β) (Set.smulSet.{u2, u3} α β _inst_1)) a (t i)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_Inter_subset Set.smul_set_interᵢ_subsetₓ'. -/
@[to_additive]
theorem smul_set_interᵢ_subset (a : α) (t : ι → Set β) : (a • ⋂ i, t i) ⊆ ⋂ i, a • t i :=
  image_interᵢ_subset _ _
#align set.smul_set_Inter_subset Set.smul_set_interᵢ_subset
#align set.vadd_set_Inter_subset Set.vadd_set_interᵢ_subset

/- warning: set.smul_set_Inter₂_subset -> Set.smul_set_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : SMul.{u1, u2} α β] (a : α) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : SMul.{u3, u4} α β] (a : α) (t : forall (i : ι), (κ i) -> (Set.{u4} β)), HasSubset.Subset.{u4} (Set.{u4} β) (Set.instHasSubsetSet.{u4} β) (HSMul.hSMul.{u3, u4, u4} α (Set.{u4} β) (Set.{u4} β) (instHSMul.{u3, u4} α (Set.{u4} β) (Set.smulSet.{u3, u4} α β _inst_1)) a (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => HSMul.hSMul.{u3, u4, u4} α (Set.{u4} β) (Set.{u4} β) (instHSMul.{u3, u4} α (Set.{u4} β) (Set.smulSet.{u3, u4} α β _inst_1)) a (t i j))))
Case conversion may be inaccurate. Consider using '#align set.smul_set_Inter₂_subset Set.smul_set_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[to_additive]
theorem smul_set_interᵢ₂_subset (a : α) (t : ∀ i, κ i → Set β) :
    (a • ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), a • t i j :=
  image_interᵢ₂_subset _ _
#align set.smul_set_Inter₂_subset Set.smul_set_interᵢ₂_subset
#align set.vadd_set_Inter₂_subset Set.vadd_set_interᵢ₂_subset

#print Set.Nonempty.smul_set /-
@[to_additive]
theorem Nonempty.smul_set : s.Nonempty → (a • s).Nonempty :=
  Nonempty.image _
#align set.nonempty.smul_set Set.Nonempty.smul_set
#align set.nonempty.vadd_set Set.Nonempty.vadd_set
-/

end HasSmulSet

section Mul

variable [Mul α] {s t u : Set α} {a : α}

#print Set.op_smul_set_subset_mul /-
@[to_additive]
theorem op_smul_set_subset_mul : a ∈ t → op a • s ⊆ s * t :=
  image_subset_image2_left
#align set.op_smul_set_subset_mul Set.op_smul_set_subset_mul
#align set.op_vadd_set_subset_add Set.op_vadd_set_subset_add
-/

#print Set.unionᵢ_op_smul_set /-
@[simp, to_additive]
theorem unionᵢ_op_smul_set (s t : Set α) : (⋃ a ∈ t, op a • s) = s * t :=
  unionᵢ_image_right _
#align set.bUnion_op_smul_set Set.unionᵢ_op_smul_set
#align set.bUnion_op_vadd_set Set.unionᵢ_op_vadd_set
-/

#print Set.mul_subset_iff_left /-
@[to_additive]
theorem mul_subset_iff_left : s * t ⊆ u ↔ ∀ a ∈ s, a • t ⊆ u :=
  image2_subset_iff_left
#align set.mul_subset_iff_left Set.mul_subset_iff_left
#align set.add_subset_iff_left Set.add_subset_iff_left
-/

#print Set.mul_subset_iff_right /-
@[to_additive]
theorem mul_subset_iff_right : s * t ⊆ u ↔ ∀ b ∈ t, op b • s ⊆ u :=
  image2_subset_iff_right
#align set.mul_subset_iff_right Set.mul_subset_iff_right
#align set.add_subset_iff_right Set.add_subset_iff_right
-/

end Mul

variable {s s₁ s₂ : Set α} {t t₁ t₂ : Set β} {a : α} {b : β}

/- warning: set.range_smul_range -> Set.range_smul_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Type.{u3}} {κ : Type.{u4}} [_inst_1 : SMul.{u1, u2} α β] (b : ι -> α) (c : κ -> β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β _inst_1) (Set.range.{u1, succ u3} α ι b) (Set.range.{u2, succ u4} β κ c)) (Set.range.{u2, max (succ u3) (succ u4)} β (Prod.{u3, u4} ι κ) (fun (p : Prod.{u3, u4} ι κ) => SMul.smul.{u1, u2} α β _inst_1 (b (Prod.fst.{u3, u4} ι κ p)) (c (Prod.snd.{u3, u4} ι κ p))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} {ι : Type.{u4}} {κ : Type.{u3}} [_inst_1 : SMul.{u2, u1} α β] (b : ι -> α) (c : κ -> β), Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β _inst_1)) (Set.range.{u2, succ u4} α ι b) (Set.range.{u1, succ u3} β κ c)) (Set.range.{u1, max (succ u4) (succ u3)} β (Prod.{u4, u3} ι κ) (fun (p : Prod.{u4, u3} ι κ) => HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β _inst_1) (b (Prod.fst.{u4, u3} ι κ p)) (c (Prod.snd.{u4, u3} ι κ p))))
Case conversion may be inaccurate. Consider using '#align set.range_smul_range Set.range_smul_rangeₓ'. -/
@[to_additive]
theorem range_smul_range {ι κ : Type _} [SMul α β] (b : ι → α) (c : κ → β) :
    range b • range c = range fun p : ι × κ => b p.1 • c p.2 :=
  ext fun x =>
    ⟨fun hx =>
      let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := Set.mem_smul.1 hx
      ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
      fun ⟨⟨i, j⟩, h⟩ => Set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩
#align set.range_smul_range Set.range_smul_range
#align set.range_vadd_range Set.range_vadd_range

/- warning: set.smul_set_range -> Set.smul_set_range is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {a : α} [_inst_1 : SMul.{u1, u2} α β] {ι : Sort.{u3}} {f : ι -> β}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a (Set.range.{u2, u3} β ι f)) (Set.range.{u2, u3} β ι (fun (i : ι) => SMul.smul.{u1, u2} α β _inst_1 a (f i)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {a : α} [_inst_1 : SMul.{u3, u2} α β] {ι : Sort.{u1}} {f : ι -> β}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u3, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} α (Set.{u2} β) (Set.smulSet.{u3, u2} α β _inst_1)) a (Set.range.{u2, u1} β ι f)) (Set.range.{u2, u1} β ι (fun (i : ι) => HSMul.hSMul.{u3, u2, u2} α β β (instHSMul.{u3, u2} α β _inst_1) a (f i)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_range Set.smul_set_rangeₓ'. -/
@[to_additive]
theorem smul_set_range [SMul α β] {ι : Sort _} {f : ι → β} : a • range f = range fun i => a • f i :=
  (range_comp _ _).symm
#align set.smul_set_range Set.smul_set_range
#align set.vadd_set_range Set.vadd_set_range

#print Set.smulCommClass_set /-
@[to_additive]
instance smulCommClass_set [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α β (Set γ) :=
  ⟨fun _ _ => Commute.set_image <| smul_comm _ _⟩
#align set.smul_comm_class_set Set.smulCommClass_set
#align set.vadd_comm_class_set Set.vaddCommClass_set
-/

#print Set.smulCommClass_set' /-
@[to_additive]
instance smulCommClass_set' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image_image2_distrib_right <| smul_comm _⟩
#align set.smul_comm_class_set' Set.smulCommClass_set'
#align set.vadd_comm_class_set' Set.vaddCommClass_set'
-/

#print Set.smulCommClass_set'' /-
@[to_additive]
instance smulCommClass_set'' [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) β (Set γ) :=
  haveI := SMulCommClass.symm α β γ
  SMulCommClass.symm _ _ _
#align set.smul_comm_class_set'' Set.smulCommClass_set''
#align set.vadd_comm_class_set'' Set.vaddCommClass_set''
-/

#print Set.smulCommClass /-
@[to_additive]
instance smulCommClass [SMul α γ] [SMul β γ] [SMulCommClass α β γ] :
    SMulCommClass (Set α) (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_left_comm smul_comm⟩
#align set.smul_comm_class Set.smulCommClass
#align set.vadd_comm_class Set.vaddCommClass
-/

#print Set.isScalarTower /-
@[to_additive]
instance isScalarTower [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α β (Set γ)
    where smul_assoc a b T := by simp only [← image_smul, image_image, smul_assoc]
#align set.is_scalar_tower Set.isScalarTower
#align set.vadd_assoc_class Set.vAddAssocClass
-/

#print Set.isScalarTower' /-
@[to_additive]
instance isScalarTower' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower α (Set β) (Set γ) :=
  ⟨fun _ _ _ => image2_image_left_comm <| smul_assoc _⟩
#align set.is_scalar_tower' Set.isScalarTower'
#align set.vadd_assoc_class' Set.vAddAssocClass'
-/

#print Set.isScalarTower'' /-
@[to_additive]
instance isScalarTower'' [SMul α β] [SMul α γ] [SMul β γ] [IsScalarTower α β γ] :
    IsScalarTower (Set α) (Set β) (Set γ) where smul_assoc T T' T'' := image2_assoc smul_assoc
#align set.is_scalar_tower'' Set.isScalarTower''
#align set.vadd_assoc_class'' Set.vAddAssocClass''
-/

#print Set.isCentralScalar /-
@[to_additive]
instance isCentralScalar [SMul α β] [SMul αᵐᵒᵖ β] [IsCentralScalar α β] :
    IsCentralScalar α (Set β) :=
  ⟨fun a S => (congr_arg fun f => f '' S) <| funext fun _ => op_smul_eq_smul _ _⟩
#align set.is_central_scalar Set.isCentralScalar
#align set.is_central_vadd Set.isCentralVAdd
-/

#print Set.mulAction /-
/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive
      "An additive action of an additive monoid `α` on a type `β` gives an additive action\nof `set α` on `set β`"]
protected def mulAction [Monoid α] [MulAction α β] : MulAction (Set α) (Set β)
    where
  mul_smul _ _ _ := image2_assoc mul_smul
  one_smul s := image2_singleton_left.trans <| by simp_rw [one_smul, image_id']
#align set.mul_action Set.mulAction
#align set.add_action Set.addAction
-/

#print Set.mulActionSet /-
/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive
      "An additive action of an additive monoid on a type `β` gives an additive action\non `set β`."]
protected def mulActionSet [Monoid α] [MulAction α β] : MulAction α (Set β)
    where
  mul_smul := by
    intros
    simp only [← image_smul, image_image, ← mul_smul]
  one_smul := by
    intros
    simp only [← image_smul, one_smul, image_id']
#align set.mul_action_set Set.mulActionSet
#align set.add_action_set Set.addActionSet
-/

scoped[Pointwise] attribute [instance] Set.mulActionSet Set.addActionSet Set.mulAction Set.addAction

#print Set.distribMulActionSet /-
/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distribMulActionSet [Monoid α] [AddMonoid β] [DistribMulAction α β] :
    DistribMulAction α (Set β)
    where
  smul_add _ _ _ := image_image2_distrib <| smul_add _
  smul_zero _ := image_singleton.trans <| by rw [smul_zero, singleton_zero]
#align set.distrib_mul_action_set Set.distribMulActionSet
-/

#print Set.mulDistribMulActionSet /-
/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mulDistribMulActionSet [Monoid α] [Monoid β] [MulDistribMulAction α β] :
    MulDistribMulAction α (Set β)
    where
  smul_mul _ _ _ := image_image2_distrib <| smul_mul' _
  smul_one _ := image_singleton.trans <| by rw [smul_one, singleton_one]
#align set.mul_distrib_mul_action_set Set.mulDistribMulActionSet
-/

scoped[Pointwise] attribute [instance] Set.distribMulActionSet Set.mulDistribMulActionSet

instance [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors (Set α) (Set β) :=
  ⟨fun s t h => by
    by_contra' H
    have hst : (s • t).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_smul_left.subset_zero_iff, ← hst.of_smul_right.subset_zero_iff, not_subset,
      mem_zero] at H
    obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul hs ht).elim ha hb⟩

#print Set.noZeroSMulDivisors_set /-
instance noZeroSMulDivisors_set [Zero α] [Zero β] [SMul α β] [NoZeroSMulDivisors α β] :
    NoZeroSMulDivisors α (Set β) :=
  ⟨fun a s h => by
    by_contra' H
    have hst : (a • s).Nonempty := h.symm.subst zero_nonempty
    simp_rw [← hst.of_image.subset_zero_iff, not_subset, mem_zero] at H
    obtain ⟨ha, b, ht, hb⟩ := H
    exact (eq_zero_or_eq_zero_of_smul_eq_zero <| h.subset <| smul_mem_smul_set ht).elim ha hb⟩
#align set.no_zero_smul_divisors_set Set.noZeroSMulDivisors_set
-/

instance [Zero α] [Mul α] [NoZeroDivisors α] : NoZeroDivisors (Set α) :=
  ⟨fun s t h => eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end Smul

section Vsub

variable {ι : Sort _} {κ : ι → Sort _} [VSub α β] {s s₁ s₂ t t₁ t₂ : Set β} {u : Set α} {a : α}
  {b c : β}

include α

#print Set.vsub /-
instance vsub : VSub (Set α) (Set β) :=
  ⟨image2 (· -ᵥ ·)⟩
#align set.has_vsub Set.vsub
-/

/- warning: set.image2_vsub -> Set.image2_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.image2.{u2, u2, u1} β β α (VSub.vsub.{u1, u2} α β _inst_1) s t) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (Set.image2.{u1, u1, u2} β β α (VSub.vsub.{u2, u1} α β _inst_1) s t) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.image2_vsub Set.image2_vsubₓ'. -/
@[simp]
theorem image2_vsub : (image2 VSub.vsub s t : Set α) = s -ᵥ t :=
  rfl
#align set.image2_vsub Set.image2_vsub

/- warning: set.image_vsub_prod -> Set.image_vsub_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.image.{u2, u1} (Prod.{u2, u2} β β) α (fun (x : Prod.{u2, u2} β β) => VSub.vsub.{u1, u2} α β _inst_1 (Prod.fst.{u2, u2} β β x) (Prod.snd.{u2, u2} β β x)) (Set.prod.{u2, u2} β β s t)) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (Set.image.{u1, u2} (Prod.{u1, u1} β β) α (fun (x : Prod.{u1, u1} β β) => VSub.vsub.{u2, u1} α β _inst_1 (Prod.fst.{u1, u1} β β x) (Prod.snd.{u1, u1} β β x)) (Set.prod.{u1, u1} β β s t)) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.image_vsub_prod Set.image_vsub_prodₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem image_vsub_prod : (fun x : β × β => x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t :=
  image_prod _
#align set.image_vsub_prod Set.image_vsub_prod

/- warning: set.mem_vsub -> Set.mem_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Iff (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)) (Exists.{succ u2} β (fun (x : β) => Exists.{succ u2} β (fun (y : β) => And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) (And (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) (Eq.{succ u1} α (VSub.vsub.{u1, u2} α β _inst_1 x y) a)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β} {a : α}, Iff (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) a (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)) (Exists.{succ u1} β (fun (x : β) => Exists.{succ u1} β (fun (y : β) => And (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) (And (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) (Eq.{succ u2} α (VSub.vsub.{u2, u1} α β _inst_1 x y) a)))))
Case conversion may be inaccurate. Consider using '#align set.mem_vsub Set.mem_vsubₓ'. -/
theorem mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a :=
  Iff.rfl
#align set.mem_vsub Set.mem_vsub

#print Set.vsub_mem_vsub /-
theorem vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t :=
  mem_image2_of_mem hb hc
#align set.vsub_mem_vsub Set.vsub_mem_vsub
-/

#print Set.empty_vsub /-
@[simp]
theorem empty_vsub (t : Set β) : ∅ -ᵥ t = ∅ :=
  image2_empty_left
#align set.empty_vsub Set.empty_vsub
-/

#print Set.vsub_empty /-
@[simp]
theorem vsub_empty (s : Set β) : s -ᵥ ∅ = ∅ :=
  image2_empty_right
#align set.vsub_empty Set.vsub_empty
-/

/- warning: set.vsub_eq_empty -> Set.vsub_eq_empty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Iff (Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Or (Eq.{succ u2} (Set.{u2} β) s (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))) (Eq.{succ u2} (Set.{u2} β) t (EmptyCollection.emptyCollection.{u2} (Set.{u2} β) (Set.hasEmptyc.{u2} β))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Iff (Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t) (EmptyCollection.emptyCollection.{u2} (Set.{u2} α) (Set.instEmptyCollectionSet.{u2} α))) (Or (Eq.{succ u1} (Set.{u1} β) s (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))) (Eq.{succ u1} (Set.{u1} β) t (EmptyCollection.emptyCollection.{u1} (Set.{u1} β) (Set.instEmptyCollectionSet.{u1} β))))
Case conversion may be inaccurate. Consider using '#align set.vsub_eq_empty Set.vsub_eq_emptyₓ'. -/
@[simp]
theorem vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ :=
  image2_eq_empty_iff
#align set.vsub_eq_empty Set.vsub_eq_empty

/- warning: set.vsub_nonempty -> Set.vsub_nonempty is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Iff (Set.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)) (And (Set.Nonempty.{u2} β s) (Set.Nonempty.{u2} β t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Iff (Set.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)) (And (Set.Nonempty.{u1} β s) (Set.Nonempty.{u1} β t))
Case conversion may be inaccurate. Consider using '#align set.vsub_nonempty Set.vsub_nonemptyₓ'. -/
@[simp]
theorem vsub_nonempty : (s -ᵥ t : Set α).Nonempty ↔ s.Nonempty ∧ t.Nonempty :=
  image2_nonempty_iff
#align set.vsub_nonempty Set.vsub_nonempty

#print Set.Nonempty.vsub /-
theorem Nonempty.vsub : s.Nonempty → t.Nonempty → (s -ᵥ t : Set α).Nonempty :=
  Nonempty.image2
#align set.nonempty.vsub Set.Nonempty.vsub
-/

/- warning: set.nonempty.of_vsub_left -> Set.Nonempty.of_vsub_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, (Set.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)) -> (Set.Nonempty.{u2} β s)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, (Set.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)) -> (Set.Nonempty.{u1} β s)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_vsub_left Set.Nonempty.of_vsub_leftₓ'. -/
theorem Nonempty.of_vsub_left : (s -ᵥ t : Set α).Nonempty → s.Nonempty :=
  Nonempty.of_image2_left
#align set.nonempty.of_vsub_left Set.Nonempty.of_vsub_left

/- warning: set.nonempty.of_vsub_right -> Set.Nonempty.of_vsub_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, (Set.Nonempty.{u1} α (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)) -> (Set.Nonempty.{u2} β t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, (Set.Nonempty.{u2} α (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)) -> (Set.Nonempty.{u1} β t)
Case conversion may be inaccurate. Consider using '#align set.nonempty.of_vsub_right Set.Nonempty.of_vsub_rightₓ'. -/
theorem Nonempty.of_vsub_right : (s -ᵥ t : Set α).Nonempty → t.Nonempty :=
  Nonempty.of_image2_right
#align set.nonempty.of_vsub_right Set.Nonempty.of_vsub_right

#print Set.vsub_singleton /-
@[simp]
theorem vsub_singleton (s : Set β) (b : β) : s -ᵥ {b} = (· -ᵥ b) '' s :=
  image2_singleton_right
#align set.vsub_singleton Set.vsub_singleton
-/

#print Set.singleton_vsub /-
@[simp]
theorem singleton_vsub (t : Set β) (b : β) : {b} -ᵥ t = (· -ᵥ ·) b '' t :=
  image2_singleton_left
#align set.singleton_vsub Set.singleton_vsub
-/

/- warning: set.singleton_vsub_singleton -> Set.singleton_vsub_singleton is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {b : β} {c : β}, Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) b) (Singleton.singleton.{u2, u2} β (Set.{u2} β) (Set.hasSingleton.{u2} β) c)) (Singleton.singleton.{u1, u1} α (Set.{u1} α) (Set.hasSingleton.{u1} α) (VSub.vsub.{u1, u2} α β _inst_1 b c))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {b : β} {c : β}, Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) b) (Singleton.singleton.{u1, u1} β (Set.{u1} β) (Set.instSingletonSet.{u1} β) c)) (Singleton.singleton.{u2, u2} α (Set.{u2} α) (Set.instSingletonSet.{u2} α) (VSub.vsub.{u2, u1} α β _inst_1 b c))
Case conversion may be inaccurate. Consider using '#align set.singleton_vsub_singleton Set.singleton_vsub_singletonₓ'. -/
@[simp]
theorem singleton_vsub_singleton : ({b} : Set β) -ᵥ {c} = {b -ᵥ c} :=
  image2_singleton
#align set.singleton_vsub_singleton Set.singleton_vsub_singleton

#print Set.vsub_subset_vsub /-
@[mono]
theorem vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ :=
  image2_subset
#align set.vsub_subset_vsub Set.vsub_subset_vsub
-/

#print Set.vsub_subset_vsub_left /-
theorem vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ :=
  image2_subset_left
#align set.vsub_subset_vsub_left Set.vsub_subset_vsub_left
-/

#print Set.vsub_subset_vsub_right /-
theorem vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t :=
  image2_subset_right
#align set.vsub_subset_vsub_right Set.vsub_subset_vsub_right
-/

/- warning: set.vsub_subset_iff -> Set.vsub_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β} {u : Set.{u1} α}, Iff (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t) u) (forall (x : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x s) -> (forall (y : β), (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) y t) -> (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) (VSub.vsub.{u1, u2} α β _inst_1 x y) u)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β} {u : Set.{u2} α}, Iff (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t) u) (forall (x : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x s) -> (forall (y : β), (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) y t) -> (Membership.mem.{u2, u2} α (Set.{u2} α) (Set.instMembershipSet.{u2} α) (VSub.vsub.{u2, u1} α β _inst_1 x y) u)))
Case conversion may be inaccurate. Consider using '#align set.vsub_subset_iff Set.vsub_subset_iffₓ'. -/
theorem vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ x ∈ s, ∀ y ∈ t, x -ᵥ y ∈ u :=
  image2_subset_iff
#align set.vsub_subset_iff Set.vsub_subset_iff

#print Set.vsub_self_mono /-
theorem vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t :=
  vsub_subset_vsub h h
#align set.vsub_self_mono Set.vsub_self_mono
-/

/- warning: set.union_vsub -> Set.union_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s₁ : Set.{u2} β} {s₂ : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s₁ s₂) t) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₁ t) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s₁ : Set.{u1} β} {s₂ : Set.{u1} β} {t : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) s₁ s₂) t) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₁ t) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.union_vsub Set.union_vsubₓ'. -/
theorem union_vsub : s₁ ∪ s₂ -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) :=
  image2_union_left
#align set.union_vsub Set.union_vsub

/- warning: set.vsub_union -> Set.vsub_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t₁) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t₁) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.vsub_union Set.vsub_unionₓ'. -/
theorem vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) :=
  image2_union_right
#align set.vsub_union Set.vsub_union

/- warning: set.inter_vsub_subset -> Set.inter_vsub_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s₁ : Set.{u2} β} {s₂ : Set.{u2} β} {t : Set.{u2} β}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s₁ s₂) t) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₁ t) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₂ t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s₁ : Set.{u1} β} {s₂ : Set.{u1} β} {t : Set.{u1} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s₁ s₂) t) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₁ t) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₂ t))
Case conversion may be inaccurate. Consider using '#align set.inter_vsub_subset Set.inter_vsub_subsetₓ'. -/
theorem inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) :=
  image2_inter_subset_left
#align set.inter_vsub_subset Set.inter_vsub_subset

/- warning: set.vsub_inter_subset -> Set.vsub_inter_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t₁) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) t₁ t₂)) (Inter.inter.{u2} (Set.{u2} α) (Set.instInterSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t₁) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t₂))
Case conversion may be inaccurate. Consider using '#align set.vsub_inter_subset Set.vsub_inter_subsetₓ'. -/
theorem vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) :=
  image2_inter_subset_right
#align set.vsub_inter_subset Set.vsub_inter_subset

/- warning: set.inter_vsub_union_subset_union -> Set.inter_vsub_union_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s₁ : Set.{u2} β} {s₂ : Set.{u2} β} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s₁ s₂) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₁ t₁) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s₁ : Set.{u1} β} {s₂ : Set.{u1} β} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s₁ s₂) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₁ t₁) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.inter_vsub_union_subset_union Set.inter_vsub_union_subset_unionₓ'. -/
theorem inter_vsub_union_subset_union : s₁ ∩ s₂ -ᵥ (t₁ ∪ t₂) ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_inter_union_subset_union
#align set.inter_vsub_union_subset_union Set.inter_vsub_union_subset_union

/- warning: set.union_vsub_inter_subset_union -> Set.union_vsub_inter_subset_union is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s₁ : Set.{u2} β} {s₂ : Set.{u2} β} {t₁ : Set.{u2} β} {t₂ : Set.{u2} β}, HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Union.union.{u2} (Set.{u2} β) (Set.hasUnion.{u2} β) s₁ s₂) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) t₁ t₂)) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₁ t₁) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s₂ t₂))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s₁ : Set.{u1} β} {s₂ : Set.{u1} β} {t₁ : Set.{u1} β} {t₂ : Set.{u1} β}, HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) (Union.union.{u1} (Set.{u1} β) (Set.instUnionSet.{u1} β) s₁ s₂) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) t₁ t₂)) (Union.union.{u2} (Set.{u2} α) (Set.instUnionSet.{u2} α) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₁ t₁) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s₂ t₂))
Case conversion may be inaccurate. Consider using '#align set.union_vsub_inter_subset_union Set.union_vsub_inter_subset_unionₓ'. -/
theorem union_vsub_inter_subset_union : s₁ ∪ s₂ -ᵥ t₁ ∩ t₂ ⊆ s₁ -ᵥ t₁ ∪ (s₂ -ᵥ t₂) :=
  image2_union_inter_subset_union
#align set.union_vsub_inter_subset_union Set.union_vsub_inter_subset_union

/- warning: set.Union_vsub_left_image -> Set.unionᵢ_vsub_left_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (a : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a s) => Set.image.{u2, u1} β α (VSub.vsub.{u1, u2} α β _inst_1 a) t))) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α β (fun (a : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) a s) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) a s) => Set.image.{u1, u2} β α ((fun (x._@.Mathlib.Data.Set.Pointwise.SMul._hyg.6864 : β) (x._@.Mathlib.Data.Set.Pointwise.SMul._hyg.6866 : β) => VSub.vsub.{u2, u1} α β _inst_1 x._@.Mathlib.Data.Set.Pointwise.SMul._hyg.6864 x._@.Mathlib.Data.Set.Pointwise.SMul._hyg.6866) a) t))) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_vsub_left_image Set.unionᵢ_vsub_left_imageₓ'. -/
theorem unionᵢ_vsub_left_image : (⋃ a ∈ s, (· -ᵥ ·) a '' t) = s -ᵥ t :=
  unionᵢ_image_left _
#align set.Union_vsub_left_image Set.unionᵢ_vsub_left_image

/- warning: set.Union_vsub_right_image -> Set.unionᵢ_vsub_right_image is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : VSub.{u1, u2} α β] {s : Set.{u2} β} {t : Set.{u2} β}, Eq.{succ u1} (Set.{u1} α) (Set.unionᵢ.{u1, succ u2} α β (fun (a : β) => Set.unionᵢ.{u1, 0} α (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a t) (fun (H : Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) a t) => Set.image.{u2, u1} β α (fun (_x : β) => VSub.vsub.{u1, u2} α β _inst_1 _x a) s))) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s t)
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : VSub.{u2, u1} α β] {s : Set.{u1} β} {t : Set.{u1} β}, Eq.{succ u2} (Set.{u2} α) (Set.unionᵢ.{u2, succ u1} α β (fun (a : β) => Set.unionᵢ.{u2, 0} α (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) a t) (fun (H : Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) a t) => Set.image.{u1, u2} β α (fun (_x : β) => VSub.vsub.{u2, u1} α β _inst_1 _x a) s))) (VSub.vsub.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.vsub.{u2, u1} α β _inst_1) s t)
Case conversion may be inaccurate. Consider using '#align set.Union_vsub_right_image Set.unionᵢ_vsub_right_imageₓ'. -/
theorem unionᵢ_vsub_right_image : (⋃ a ∈ t, (· -ᵥ a) '' s) = s -ᵥ t :=
  unionᵢ_image_right _
#align set.Union_vsub_right_image Set.unionᵢ_vsub_right_image

/- warning: set.Union_vsub -> Set.unionᵢ_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : VSub.{u1, u2} α β] (s : ι -> (Set.{u2} β)) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : VSub.{u2, u3} α β] (s : ι -> (Set.{u3} β)) (t : Set.{u3} β), Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => s i)) t) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Union_vsub Set.unionᵢ_vsubₓ'. -/
theorem unionᵢ_vsub (s : ι → Set β) (t : Set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
  image2_unionᵢ_left _ _ _
#align set.Union_vsub Set.unionᵢ_vsub

/- warning: set.vsub_Union -> Set.vsub_unionᵢ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : VSub.{u1, u2} α β] (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : VSub.{u2, u3} α β] (s : Set.{u3} β) (t : ι -> (Set.{u3} β)), Eq.{succ u2} (Set.{u2} α) (VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) s (Set.unionᵢ.{u3, u1} β ι (fun (i : ι) => t i))) (Set.unionᵢ.{u2, u1} α ι (fun (i : ι) => VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.vsub_Union Set.vsub_unionᵢₓ'. -/
theorem vsub_unionᵢ (s : Set β) (t : ι → Set β) : (s -ᵥ ⋃ i, t i) = ⋃ i, s -ᵥ t i :=
  image2_unionᵢ_right _ _ _
#align set.vsub_Union Set.vsub_unionᵢ

/- warning: set.Union₂_vsub -> Set.unionᵢ₂_vsub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : VSub.{u1, u2} α β] (s : forall (i : ι), (κ i) -> (Set.{u2} β)) (t : Set.{u2} β), Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : VSub.{u3, u4} α β] (s : forall (i : ι), (κ i) -> (Set.{u4} β)) (t : Set.{u4} β), Eq.{succ u3} (Set.{u3} α) (VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => s i j))) t) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Union₂_vsub Set.unionᵢ₂_vsubₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem unionᵢ₂_vsub (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋃ (i) (j), s i j) -ᵥ t = ⋃ (i) (j), s i j -ᵥ t :=
  image2_unionᵢ₂_left _ _ _
#align set.Union₂_vsub Set.unionᵢ₂_vsub

/- warning: set.vsub_Union₂ -> Set.vsub_unionᵢ₂ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : VSub.{u1, u2} α β] (s : Set.{u2} β) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), Eq.{succ u1} (Set.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Set.unionᵢ.{u2, u3} β ι (fun (i : ι) => Set.unionᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u1, u3} α ι (fun (i : ι) => Set.unionᵢ.{u1, u4} α (κ i) (fun (j : κ i) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : VSub.{u3, u4} α β] (s : Set.{u4} β) (t : forall (i : ι), (κ i) -> (Set.{u4} β)), Eq.{succ u3} (Set.{u3} α) (VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) s (Set.unionᵢ.{u4, u2} β ι (fun (i : ι) => Set.unionᵢ.{u4, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.unionᵢ.{u3, u2} α ι (fun (i : ι) => Set.unionᵢ.{u3, u1} α (κ i) (fun (j : κ i) => VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.vsub_Union₂ Set.vsub_unionᵢ₂ₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_unionᵢ₂ (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋃ (i) (j), t i j) = ⋃ (i) (j), s -ᵥ t i j :=
  image2_unionᵢ₂_right _ _ _
#align set.vsub_Union₂ Set.vsub_unionᵢ₂

/- warning: set.Inter_vsub_subset -> Set.interᵢ_vsub_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : VSub.{u1, u2} α β] (s : ι -> (Set.{u2} β)) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (s i) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : VSub.{u2, u3} α β] (s : ι -> (Set.{u3} β)) (t : Set.{u3} β), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => s i)) t) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) (s i) t))
Case conversion may be inaccurate. Consider using '#align set.Inter_vsub_subset Set.interᵢ_vsub_subsetₓ'. -/
theorem interᵢ_vsub_subset (s : ι → Set β) (t : Set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
  image2_interᵢ_subset_left _ _ _
#align set.Inter_vsub_subset Set.interᵢ_vsub_subset

/- warning: set.vsub_Inter_subset -> Set.vsub_interᵢ_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} [_inst_1 : VSub.{u1, u2} α β] (s : Set.{u2} β) (t : ι -> (Set.{u2} β)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (t i)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u3}} {ι : Sort.{u1}} [_inst_1 : VSub.{u2, u3} α β] (s : Set.{u3} β) (t : ι -> (Set.{u3} β)), HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) (VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) s (Set.interᵢ.{u3, u1} β ι (fun (i : ι) => t i))) (Set.interᵢ.{u2, u1} α ι (fun (i : ι) => VSub.vsub.{u2, u3} (Set.{u2} α) (Set.{u3} β) (Set.vsub.{u2, u3} α β _inst_1) s (t i)))
Case conversion may be inaccurate. Consider using '#align set.vsub_Inter_subset Set.vsub_interᵢ_subsetₓ'. -/
theorem vsub_interᵢ_subset (s : Set β) (t : ι → Set β) : (s -ᵥ ⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
  image2_interᵢ_subset_right _ _ _
#align set.vsub_Inter_subset Set.vsub_interᵢ_subset

/- warning: set.Inter₂_vsub_subset -> Set.interᵢ₂_vsub_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : VSub.{u1, u2} α β] (s : forall (i : ι), (κ i) -> (Set.{u2} β)) (t : Set.{u2} β), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) (s i j) t)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : VSub.{u3, u4} α β] (s : forall (i : ι), (κ i) -> (Set.{u4} β)) (t : Set.{u4} β), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => s i j))) t) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) (s i j) t)))
Case conversion may be inaccurate. Consider using '#align set.Inter₂_vsub_subset Set.interᵢ₂_vsub_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem interᵢ₂_vsub_subset (s : ∀ i, κ i → Set β) (t : Set β) :
    (⋂ (i) (j), s i j) -ᵥ t ⊆ ⋂ (i) (j), s i j -ᵥ t :=
  image2_interᵢ₂_subset_left _ _ _
#align set.Inter₂_vsub_subset Set.interᵢ₂_vsub_subset

/- warning: set.vsub_Inter₂_subset -> Set.vsub_interᵢ₂_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {ι : Sort.{u3}} {κ : ι -> Sort.{u4}} [_inst_1 : VSub.{u1, u2} α β] (s : Set.{u2} β) (t : forall (i : ι), (κ i) -> (Set.{u2} β)), HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) (VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (Set.interᵢ.{u2, u3} β ι (fun (i : ι) => Set.interᵢ.{u2, u4} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u1, u3} α ι (fun (i : ι) => Set.interᵢ.{u1, u4} α (κ i) (fun (j : κ i) => VSub.vsub.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.vsub.{u1, u2} α β _inst_1) s (t i j))))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u4}} {ι : Sort.{u2}} {κ : ι -> Sort.{u1}} [_inst_1 : VSub.{u3, u4} α β] (s : Set.{u4} β) (t : forall (i : ι), (κ i) -> (Set.{u4} β)), HasSubset.Subset.{u3} (Set.{u3} α) (Set.instHasSubsetSet.{u3} α) (VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) s (Set.interᵢ.{u4, u2} β ι (fun (i : ι) => Set.interᵢ.{u4, u1} β (κ i) (fun (j : κ i) => t i j)))) (Set.interᵢ.{u3, u2} α ι (fun (i : ι) => Set.interᵢ.{u3, u1} α (κ i) (fun (j : κ i) => VSub.vsub.{u3, u4} (Set.{u3} α) (Set.{u4} β) (Set.vsub.{u3, u4} α β _inst_1) s (t i j))))
Case conversion may be inaccurate. Consider using '#align set.vsub_Inter₂_subset Set.vsub_interᵢ₂_subsetₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem vsub_interᵢ₂_subset (s : Set β) (t : ∀ i, κ i → Set β) :
    (s -ᵥ ⋂ (i) (j), t i j) ⊆ ⋂ (i) (j), s -ᵥ t i j :=
  image2_interᵢ₂_subset_right _ _ _
#align set.vsub_Inter₂_subset Set.vsub_interᵢ₂_subset

end Vsub

open Pointwise

/- warning: set.image_smul_comm -> Set.image_smul_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SMul.{u1, u2} α β] [_inst_2 : SMul.{u1, u3} α γ] (f : β -> γ) (a : α) (s : Set.{u2} β), (forall (b : β), Eq.{succ u3} γ (f (SMul.smul.{u1, u2} α β _inst_1 a b)) (SMul.smul.{u1, u3} α γ _inst_2 a (f b))) -> (Eq.{succ u3} (Set.{u3} γ) (Set.image.{u2, u3} β γ f (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β _inst_1) a s)) (SMul.smul.{u1, u3} α (Set.{u3} γ) (Set.smulSet.{u1, u3} α γ _inst_2) a (Set.image.{u2, u3} β γ f s)))
but is expected to have type
  forall {α : Type.{u3}} {β : Type.{u2}} {γ : Type.{u1}} [_inst_1 : SMul.{u3, u2} α β] [_inst_2 : SMul.{u3, u1} α γ] (f : β -> γ) (a : α) (s : Set.{u2} β), (forall (b : β), Eq.{succ u1} γ (f (HSMul.hSMul.{u3, u2, u2} α β β (instHSMul.{u3, u2} α β _inst_1) a b)) (HSMul.hSMul.{u3, u1, u1} α γ γ (instHSMul.{u3, u1} α γ _inst_2) a (f b))) -> (Eq.{succ u1} (Set.{u1} γ) (Set.image.{u2, u1} β γ f (HSMul.hSMul.{u3, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u3, u2} α (Set.{u2} β) (Set.smulSet.{u3, u2} α β _inst_1)) a s)) (HSMul.hSMul.{u3, u1, u1} α (Set.{u1} γ) (Set.{u1} γ) (instHSMul.{u3, u1} α (Set.{u1} γ) (Set.smulSet.{u3, u1} α γ _inst_2)) a (Set.image.{u2, u1} β γ f s)))
Case conversion may be inaccurate. Consider using '#align set.image_smul_comm Set.image_smul_commₓ'. -/
@[to_additive]
theorem image_smul_comm [SMul α β] [SMul α γ] (f : β → γ) (a : α) (s : Set β) :
    (∀ b, f (a • b) = a • f b) → f '' (a • s) = a • f '' s :=
  image_comm
#align set.image_smul_comm Set.image_smul_comm
#align set.image_vadd_comm Set.image_vadd_comm

/- warning: set.image_smul_distrib -> Set.image_smul_distrib is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} {α : Type.{u2}} {β : Type.{u3}} [_inst_1 : MulOneClass.{u2} α] [_inst_2 : MulOneClass.{u3} β] [_inst_3 : MonoidHomClass.{u1, u2, u3} F α β _inst_1 _inst_2] (f : F) (a : α) (s : Set.{u2} α), Eq.{succ u3} (Set.{u3} β) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α _inst_1) (MulOneClass.toHasMul.{u3} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f) (SMul.smul.{u2, u2} α (Set.{u2} α) (Set.smulSet.{u2, u2} α α (Mul.toSMul.{u2} α (MulOneClass.toHasMul.{u2} α _inst_1))) a s)) (SMul.smul.{u3, u3} β (Set.{u3} β) (Set.smulSet.{u3, u3} β β (Mul.toSMul.{u3} β (MulOneClass.toHasMul.{u3} β _inst_2))) (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α _inst_1) (MulOneClass.toHasMul.{u3} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f a) (Set.image.{u2, u3} α β (coeFn.{succ u1, max (succ u2) (succ u3)} F (fun (_x : F) => α -> β) (FunLike.hasCoeToFun.{succ u1, succ u2, succ u3} F α (fun (_x : α) => β) (MulHomClass.toFunLike.{u1, u2, u3} F α β (MulOneClass.toHasMul.{u2} α _inst_1) (MulOneClass.toHasMul.{u3} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u2, u3} F α β _inst_1 _inst_2 _inst_3))) f) s))
but is expected to have type
  forall {F : Type.{u1}} {α : Type.{u3}} {β : Type.{u2}} [_inst_1 : MulOneClass.{u3} α] [_inst_2 : MulOneClass.{u2} β] [_inst_3 : MonoidHomClass.{u1, u3, u2} F α β _inst_1 _inst_2] (f : F) (a : α) (s : Set.{u3} α), Eq.{succ u2} (Set.{u2} β) (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α _inst_1) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3)) f) (HSMul.hSMul.{u3, u3, u3} α (Set.{u3} α) (Set.{u3} α) (instHSMul.{u3, u3} α (Set.{u3} α) (Set.smulSet.{u3, u3} α α (Mul.toSMul.{u3} α (MulOneClass.toMul.{u3} α _inst_1)))) a s)) (HSMul.hSMul.{u2, u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) a) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) a) (Set.{u2} β) (Set.smulSet.{u2, u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) a) β (Mul.toSMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) a) (MulOneClass.toMul.{u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) a) _inst_2)))) (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α _inst_1) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3)) f a) (Set.image.{u3, u2} α β (FunLike.coe.{succ u1, succ u3, succ u2} F α (fun (_x : α) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2391 : α) => β) _x) (MulHomClass.toFunLike.{u1, u3, u2} F α β (MulOneClass.toMul.{u3} α _inst_1) (MulOneClass.toMul.{u2} β _inst_2) (MonoidHomClass.toMulHomClass.{u1, u3, u2} F α β _inst_1 _inst_2 _inst_3)) f) s))
Case conversion may be inaccurate. Consider using '#align set.image_smul_distrib Set.image_smul_distribₓ'. -/
@[to_additive]
theorem image_smul_distrib [MulOneClass α] [MulOneClass β] [MonoidHomClass F α β] (f : F) (a : α)
    (s : Set α) : f '' (a • s) = f a • f '' s :=
  image_comm <| map_mul _ _
#align set.image_smul_distrib Set.image_smul_distrib
#align set.image_vadd_distrib Set.image_vadd_distrib

section SMul

variable [SMul αᵐᵒᵖ β] [SMul β γ] [SMul α γ]

/- warning: set.op_smul_set_smul_eq_smul_smul_set -> Set.op_smul_set_smul_eq_smul_smul_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} {γ : Type.{u3}} [_inst_1 : SMul.{u1, u2} (MulOpposite.{u1} α) β] [_inst_2 : SMul.{u2, u3} β γ] [_inst_3 : SMul.{u1, u3} α γ] (a : α) (s : Set.{u2} β) (t : Set.{u3} γ), (forall (a : α) (b : β) (c : γ), Eq.{succ u3} γ (SMul.smul.{u2, u3} β γ _inst_2 (SMul.smul.{u1, u2} (MulOpposite.{u1} α) β _inst_1 (MulOpposite.op.{u1} α a) b) c) (SMul.smul.{u2, u3} β γ _inst_2 b (SMul.smul.{u1, u3} α γ _inst_3 a c))) -> (Eq.{succ u3} (Set.{u3} γ) (SMul.smul.{u2, u3} (Set.{u2} β) (Set.{u3} γ) (Set.smul.{u2, u3} β γ _inst_2) (SMul.smul.{u1, u2} (MulOpposite.{u1} α) (Set.{u2} β) (Set.smulSet.{u1, u2} (MulOpposite.{u1} α) β _inst_1) (MulOpposite.op.{u1} α a) s) t) (SMul.smul.{u2, u3} (Set.{u2} β) (Set.{u3} γ) (Set.smul.{u2, u3} β γ _inst_2) s (SMul.smul.{u1, u3} α (Set.{u3} γ) (Set.smulSet.{u1, u3} α γ _inst_3) a t)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u3}} {γ : Type.{u2}} [_inst_1 : SMul.{u1, u3} (MulOpposite.{u1} α) β] [_inst_2 : SMul.{u3, u2} β γ] [_inst_3 : SMul.{u1, u2} α γ] (a : α) (s : Set.{u3} β) (t : Set.{u2} γ), (forall (a : α) (b : β) (c : γ), Eq.{succ u2} γ (HSMul.hSMul.{u3, u2, u2} β γ γ (instHSMul.{u3, u2} β γ _inst_2) (HSMul.hSMul.{u1, u3, u3} (MulOpposite.{u1} α) β β (instHSMul.{u1, u3} (MulOpposite.{u1} α) β _inst_1) (MulOpposite.op.{u1} α a) b) c) (HSMul.hSMul.{u3, u2, u2} β γ γ (instHSMul.{u3, u2} β γ _inst_2) b (HSMul.hSMul.{u1, u2, u2} α γ γ (instHSMul.{u1, u2} α γ _inst_3) a c))) -> (Eq.{succ u2} (Set.{u2} γ) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} β) (Set.{u2} γ) (Set.{u2} γ) (instHSMul.{u3, u2} (Set.{u3} β) (Set.{u2} γ) (Set.smul.{u3, u2} β γ _inst_2)) (HSMul.hSMul.{u1, u3, u3} (MulOpposite.{u1} α) (Set.{u3} β) (Set.{u3} β) (instHSMul.{u1, u3} (MulOpposite.{u1} α) (Set.{u3} β) (Set.smulSet.{u1, u3} (MulOpposite.{u1} α) β _inst_1)) (MulOpposite.op.{u1} α a) s) t) (HSMul.hSMul.{u3, u2, u2} (Set.{u3} β) (Set.{u2} γ) (Set.{u2} γ) (instHSMul.{u3, u2} (Set.{u3} β) (Set.{u2} γ) (Set.smul.{u3, u2} β γ _inst_2)) s (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} γ) (Set.{u2} γ) (instHSMul.{u1, u2} α (Set.{u2} γ) (Set.smulSet.{u1, u2} α γ _inst_3)) a t)))
Case conversion may be inaccurate. Consider using '#align set.op_smul_set_smul_eq_smul_smul_set Set.op_smul_set_smul_eq_smul_smul_setₓ'. -/
-- TODO: replace hypothesis and conclusion with a typeclass
@[to_additive]
theorem op_smul_set_smul_eq_smul_smul_set (a : α) (s : Set β) (t : Set γ)
    (h : ∀ (a : α) (b : β) (c : γ), (op a • b) • c = b • a • c) : (op a • s) • t = s • a • t :=
  by
  ext
  simp [mem_smul, mem_smul_set, h]
#align set.op_smul_set_smul_eq_smul_smul_set Set.op_smul_set_smul_eq_smul_smul_set
#align set.op_vadd_set_vadd_eq_vadd_vadd_set Set.op_vadd_set_vadd_eq_vadd_vadd_set

end SMul

section SMulWithZero

variable [Zero α] [Zero β] [SMulWithZero α β] {s : Set α} {t : Set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/


/- warning: set.smul_zero_subset -> Set.smul_zero_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] (s : Set.{u1} α), HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) s (OfNat.ofNat.{u2} (Set.{u2} β) 0 (OfNat.mk.{u2} (Set.{u2} β) 0 (Zero.zero.{u2} (Set.{u2} β) (Set.zero.{u2} β _inst_2))))) (OfNat.ofNat.{u2} (Set.{u2} β) 0 (OfNat.mk.{u2} (Set.{u2} β) 0 (Zero.zero.{u2} (Set.{u2} β) (Set.zero.{u2} β _inst_2))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] (s : Set.{u2} α), HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) s (OfNat.ofNat.{u1} (Set.{u1} β) 0 (Zero.toOfNat0.{u1} (Set.{u1} β) (Set.zero.{u1} β _inst_2)))) (OfNat.ofNat.{u1} (Set.{u1} β) 0 (Zero.toOfNat0.{u1} (Set.{u1} β) (Set.zero.{u1} β _inst_2)))
Case conversion may be inaccurate. Consider using '#align set.smul_zero_subset Set.smul_zero_subsetₓ'. -/
theorem smul_zero_subset (s : Set α) : s • (0 : Set β) ⊆ 0 := by simp [subset_def, mem_smul]
#align set.smul_zero_subset Set.smul_zero_subset

#print Set.zero_smul_subset /-
theorem zero_smul_subset (t : Set β) : (0 : Set α) • t ⊆ 0 := by simp [subset_def, mem_smul]
#align set.zero_smul_subset Set.zero_smul_subset
-/

/- warning: set.nonempty.smul_zero -> Set.Nonempty.smul_zero is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) s (OfNat.ofNat.{u2} (Set.{u2} β) 0 (OfNat.mk.{u2} (Set.{u2} β) 0 (Zero.zero.{u2} (Set.{u2} β) (Set.zero.{u2} β _inst_2))))) (OfNat.ofNat.{u2} (Set.{u2} β) 0 (OfNat.mk.{u2} (Set.{u2} β) 0 (Zero.zero.{u2} (Set.{u2} β) (Set.zero.{u2} β _inst_2)))))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) s (OfNat.ofNat.{u1} (Set.{u1} β) 0 (Zero.toOfNat0.{u1} (Set.{u1} β) (Set.zero.{u1} β _inst_2)))) (OfNat.ofNat.{u1} (Set.{u1} β) 0 (Zero.toOfNat0.{u1} (Set.{u1} β) (Set.zero.{u1} β _inst_2))))
Case conversion may be inaccurate. Consider using '#align set.nonempty.smul_zero Set.Nonempty.smul_zeroₓ'. -/
theorem Nonempty.smul_zero (hs : s.Nonempty) : s • (0 : Set β) = 0 :=
  s.smul_zero_subset.antisymm <| by simpa [mem_smul] using hs
#align set.nonempty.smul_zero Set.Nonempty.smul_zero

#print Set.Nonempty.zero_smul /-
theorem Nonempty.zero_smul (ht : t.Nonempty) : (0 : Set α) • t = 0 :=
  t.zero_smul_subset.antisymm <| by simpa [mem_smul] using ht
#align set.nonempty.zero_smul Set.Nonempty.zero_smul
-/

#print Set.zero_smul_set /-
/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
theorem zero_smul_set {s : Set β} (h : s.Nonempty) : (0 : α) • s = (0 : Set β) := by
  simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]
#align set.zero_smul_set Set.zero_smul_set
-/

#print Set.zero_smul_set_subset /-
theorem zero_smul_set_subset (s : Set β) : (0 : α) • s ⊆ 0 :=
  image_subset_iff.2 fun x _ => zero_smul α x
#align set.zero_smul_set_subset Set.zero_smul_set_subset
-/

#print Set.subsingleton_zero_smul_set /-
theorem subsingleton_zero_smul_set (s : Set β) : ((0 : α) • s).Subsingleton :=
  subsingleton_singleton.anti <| zero_smul_set_subset s
#align set.subsingleton_zero_smul_set Set.subsingleton_zero_smul_set
-/

#print Set.zero_mem_smul_set /-
theorem zero_mem_smul_set {t : Set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
  ⟨0, h, smul_zero _⟩
#align set.zero_mem_smul_set Set.zero_mem_smul_set
-/

variable [NoZeroSMulDivisors α β] {a : α}

#print Set.zero_mem_smul_iff /-
theorem zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.Nonempty ∨ (0 : β) ∈ t ∧ s.Nonempty :=
  by
  constructor
  · rintro ⟨a, b, ha, hb, h⟩
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h
    · exact Or.inl ⟨ha, b, hb⟩
    · exact Or.inr ⟨hb, a, ha⟩
  · rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩)
    · exact ⟨0, b, hs, hb, zero_smul _ _⟩
    · exact ⟨a, 0, ha, ht, smul_zero _⟩
#align set.zero_mem_smul_iff Set.zero_mem_smul_iff
-/

/- warning: set.zero_mem_smul_set_iff -> Set.zero_mem_smul_set_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Zero.{u1} α] [_inst_2 : Zero.{u2} β] [_inst_3 : SMulWithZero.{u1, u2} α β _inst_1 _inst_2] {t : Set.{u2} β} [_inst_4 : NoZeroSMulDivisors.{u1, u2} α β _inst_1 _inst_2 (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α _inst_1)))) -> (Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β _inst_2 (SMulWithZero.toSmulZeroClass.{u1, u2} α β _inst_1 _inst_2 _inst_3))) a t)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (OfNat.ofNat.{u2} β 0 (OfNat.mk.{u2} β 0 (Zero.zero.{u2} β _inst_2))) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Zero.{u2} α] [_inst_2 : Zero.{u1} β] [_inst_3 : SMulWithZero.{u2, u1} α β _inst_1 _inst_2] {t : Set.{u1} β} [_inst_4 : NoZeroSMulDivisors.{u2, u1} α β _inst_1 _inst_2 (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α _inst_1))) -> (Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2)) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (SMulZeroClass.toSMul.{u2, u1} α β _inst_2 (SMulWithZero.toSMulZeroClass.{u2, u1} α β _inst_1 _inst_2 _inst_3)))) a t)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (OfNat.ofNat.{u1} β 0 (Zero.toOfNat0.{u1} β _inst_2)) t))
Case conversion may be inaccurate. Consider using '#align set.zero_mem_smul_set_iff Set.zero_mem_smul_set_iffₓ'. -/
theorem zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
  by
  refine' ⟨_, zero_mem_smul_set⟩
  rintro ⟨b, hb, h⟩
  rwa [(eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha] at hb
#align set.zero_mem_smul_set_iff Set.zero_mem_smul_set_iff

end SMulWithZero

section Semigroup

variable [Semigroup α]

/- warning: set.op_smul_set_mul_eq_mul_smul_set -> Set.op_smul_set_mul_eq_mul_smul_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (SMul.smul.{u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.smulSet.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) (MulOpposite.op.{u1} α a) s) t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) s (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α _inst_1))) a t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] (a : α) (s : Set.{u1} α) (t : Set.{u1} α), Eq.{succ u1} (Set.{u1} α) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Semigroup.toMul.{u1} α _inst_1))) (HSMul.hSMul.{u1, u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.smulSet.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)))) (MulOpposite.op.{u1} α a) s) t) (HMul.hMul.{u1, u1, u1} (Set.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHMul.{u1} (Set.{u1} α) (Set.mul.{u1} α (Semigroup.toMul.{u1} α _inst_1))) s (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α _inst_1)))) a t))
Case conversion may be inaccurate. Consider using '#align set.op_smul_set_mul_eq_mul_smul_set Set.op_smul_set_mul_eq_mul_smul_setₓ'. -/
@[to_additive]
theorem op_smul_set_mul_eq_mul_smul_set (a : α) (s : Set α) (t : Set α) :
    op a • s * t = s * a • t :=
  op_smul_set_smul_eq_smul_smul_set _ _ _ fun _ _ _ => mul_assoc _ _ _
#align set.op_smul_set_mul_eq_mul_smul_set Set.op_smul_set_mul_eq_mul_smul_set
#align set.op_vadd_set_add_eq_add_vadd_set Set.op_vadd_set_add_eq_add_vadd_set

end Semigroup

section LeftCancelSemigroup

variable [LeftCancelSemigroup α] {s t : Set α}

/- warning: set.pairwise_disjoint_smul_iff -> Set.pairwiseDisjoint_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) α (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.completeBooleanAlgebra.{u1} α)))))) (GeneralizedBooleanAlgebra.toOrderBot.{u1} (Set.{u1} α) (BooleanAlgebra.toGeneralizedBooleanAlgebra.{u1} (Set.{u1} α) (Set.booleanAlgebra.{u1} α))) s (fun (_x : α) => SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1)))) _x t)) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toHasMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Set.prod.{u1, u1} α α s t))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : LeftCancelSemigroup.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α}, Iff (Set.PairwiseDisjoint.{u1, u1} (Set.{u1} α) α (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) (BoundedOrder.toOrderBot.{u1} (Set.{u1} α) (Preorder.toLE.{u1} (Set.{u1} α) (PartialOrder.toPreorder.{u1} (Set.{u1} α) (CompleteSemilatticeInf.toPartialOrder.{u1} (Set.{u1} α) (CompleteLattice.toCompleteSemilatticeInf.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))))) (CompleteLattice.toBoundedOrder.{u1} (Set.{u1} α) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} α) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} α) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} α) (Set.instCompleteBooleanAlgebraSet.{u1} α)))))) s (fun (_x : α) => HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))))) _x t)) (Set.InjOn.{u1, u1} (Prod.{u1, u1} α α) α (fun (p : Prod.{u1, u1} α α) => HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Semigroup.toMul.{u1} α (LeftCancelSemigroup.toSemigroup.{u1} α _inst_1))) (Prod.fst.{u1, u1} α α p) (Prod.snd.{u1, u1} α α p)) (Set.prod.{u1, u1} α α s t))
Case conversion may be inaccurate. Consider using '#align set.pairwise_disjoint_smul_iff Set.pairwiseDisjoint_smul_iffₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[to_additive]
theorem pairwiseDisjoint_smul_iff :
    s.PairwiseDisjoint (· • t) ↔ (s ×ˢ t).InjOn fun p => p.1 * p.2 :=
  pairwiseDisjoint_image_right_iff fun _ _ => mul_right_injective _
#align set.pairwise_disjoint_smul_iff Set.pairwiseDisjoint_smul_iff
#align set.pairwise_disjoint_vadd_iff Set.pairwiseDisjoint_vadd_iff

end LeftCancelSemigroup

section Group

variable [Group α] [MulAction α β] {s t A B : Set β} {a : α} {x : β}

#print Set.smul_mem_smul_set_iff /-
@[simp, to_additive]
theorem smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s :=
  (MulAction.injective _).mem_set_image
#align set.smul_mem_smul_set_iff Set.smul_mem_smul_set_iff
#align set.vadd_mem_vadd_set_iff Set.vadd_mem_vadd_set_iff
-/

/- warning: set.mem_smul_set_iff_inv_smul_mem -> Set.mem_smul_set_iff_inv_smul_mem is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {a : α} {x : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a A)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) x) A)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {a : α} {x : β}, Iff (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a A)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) x) A)
Case conversion may be inaccurate. Consider using '#align set.mem_smul_set_iff_inv_smul_mem Set.mem_smul_set_iff_inv_smul_memₓ'. -/
@[to_additive]
theorem mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show x ∈ MulAction.toPerm a '' A ↔ _ from mem_image_equiv
#align set.mem_smul_set_iff_inv_smul_mem Set.mem_smul_set_iff_inv_smul_mem
#align set.mem_vadd_set_iff_neg_vadd_mem Set.mem_vadd_set_iff_neg_vadd_mem

/- warning: set.mem_inv_smul_set_iff -> Set.mem_inv_smul_set_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {a : α} {x : β}, Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) A)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a x) A)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {a : α} {x : β}, Iff (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) x (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) A)) (Membership.mem.{u2, u2} β (Set.{u2} β) (Set.instMembershipSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a x) A)
Case conversion may be inaccurate. Consider using '#align set.mem_inv_smul_set_iff Set.mem_inv_smul_set_iffₓ'. -/
@[to_additive]
theorem mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A := by
  simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]
#align set.mem_inv_smul_set_iff Set.mem_inv_smul_set_iff
#align set.mem_neg_vadd_set_iff Set.mem_neg_vadd_set_iff

/- warning: set.preimage_smul -> Set.preimage_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) a x) t) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a x) t) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) t)
Case conversion may be inaccurate. Consider using '#align set.preimage_smul Set.preimage_smulₓ'. -/
@[to_additive]
theorem preimage_smul (a : α) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  ((MulAction.toPerm a).symm.image_eq_preimage _).symm
#align set.preimage_smul Set.preimage_smul
#align set.preimage_vadd Set.preimage_vadd

/- warning: set.preimage_smul_inv -> Set.preimage_smul_inv is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) x) t) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a t)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => HSMul.hSMul.{u1, u2, u2} α β β (instHSMul.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) x) t) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a t)
Case conversion may be inaccurate. Consider using '#align set.preimage_smul_inv Set.preimage_smul_invₓ'. -/
@[to_additive]
theorem preimage_smul_inv (a : α) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (toUnits a)⁻¹ t
#align set.preimage_smul_inv Set.preimage_smul_inv
#align set.preimage_vadd_neg Set.preimage_vadd_neg

#print Set.set_smul_subset_set_smul_iff /-
@[simp, to_additive]
theorem set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
  image_subset_image_iff <| MulAction.injective _
#align set.set_smul_subset_set_smul_iff Set.set_smul_subset_set_smul_iff
#align set.set_vadd_subset_set_vadd_iff Set.set_vadd_subset_set_vadd_iff
-/

/- warning: set.set_smul_subset_iff -> Set.set_smul_subset_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {B : Set.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a A) B) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) A (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) B))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {B : Set.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a A) B) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) A (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) B))
Case conversion may be inaccurate. Consider using '#align set.set_smul_subset_iff Set.set_smul_subset_iffₓ'. -/
@[to_additive]
theorem set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  image_subset_iff.trans <|
    iff_of_eq <| congr_arg _ <| preimage_equiv_eq_image_symm _ <| MulAction.toPerm _
#align set.set_smul_subset_iff Set.set_smul_subset_iff
#align set.set_vadd_subset_iff Set.set_vadd_subset_iff

/- warning: set.subset_set_smul_iff -> Set.subset_set_smul_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {B : Set.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) A (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a B)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) A) B)
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {A : Set.{u2} β} {B : Set.{u2} β} {a : α}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) A (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a B)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.instHasSubsetSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) A) B)
Case conversion may be inaccurate. Consider using '#align set.subset_set_smul_iff Set.subset_set_smul_iffₓ'. -/
@[to_additive]
theorem subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  Iff.symm <|
    image_subset_iff.trans <|
      Iff.symm <| iff_of_eq <| congr_arg _ <| image_equiv_eq_preimage_symm _ <| MulAction.toPerm _
#align set.subset_set_smul_iff Set.subset_set_smul_iff
#align set.subset_set_vadd_iff Set.subset_set_vadd_iff

/- warning: set.smul_set_inter -> Set.smul_set_inter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.instInterSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a t))
Case conversion may be inaccurate. Consider using '#align set.smul_set_inter Set.smul_set_interₓ'. -/
@[to_additive]
theorem smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
  image_inter <| MulAction.injective a
#align set.smul_set_inter Set.smul_set_inter
#align set.vadd_set_inter Set.vadd_set_inter

/- warning: set.smul_set_sdiff -> Set.smul_set_sdiff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s t)) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) s t)) (SDiff.sdiff.{u2} (Set.{u2} β) (Set.instSDiffSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a t))
Case conversion may be inaccurate. Consider using '#align set.smul_set_sdiff Set.smul_set_sdiffₓ'. -/
@[to_additive]
theorem smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective a) _ _
#align set.smul_set_sdiff Set.smul_set_sdiff
#align set.vadd_set_sdiff Set.vadd_set_sdiff

/- warning: set.smul_set_symm_diff -> Set.smul_set_symm_diff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s t)) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (Set.instSDiffSet.{u2} β) s t)) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.instCompleteBooleanAlgebraSet.{u2} β))))))) (Set.instSDiffSet.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) a t))
Case conversion may be inaccurate. Consider using '#align set.smul_set_symm_diff Set.smul_set_symm_diffₓ'. -/
@[to_additive]
theorem smul_set_symm_diff : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symm_diff (MulAction.injective a) _ _
#align set.smul_set_symm_diff Set.smul_set_symm_diff
#align set.vadd_set_symm_diff Set.vadd_set_symm_diff

#print Set.smul_set_univ /-
@[simp, to_additive]
theorem smul_set_univ : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective a
#align set.smul_set_univ Set.smul_set_univ
#align set.vadd_set_univ Set.vadd_set_univ
-/

/- warning: set.smul_univ -> Set.smul_univ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u1} α}, (Set.Nonempty.{u1} α s) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) s (Set.univ.{u2} β)) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : Group.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1))] {s : Set.{u2} α}, (Set.Nonempty.{u2} α s) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (DivInvMonoid.toMonoid.{u2} α (Group.toDivInvMonoid.{u2} α _inst_1)) _inst_2))) s (Set.univ.{u1} β)) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.smul_univ Set.smul_univₓ'. -/
@[simp, to_additive]
theorem smul_univ {s : Set α} (hs : s.Nonempty) : s • (univ : Set β) = univ :=
  let ⟨a, ha⟩ := hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩
#align set.smul_univ Set.smul_univ
#align set.vadd_univ Set.vadd_univ

/- warning: set.smul_inter_ne_empty_iff -> Set.smul_inter_ne_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) b)) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) a (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) b)) x))))
Case conversion may be inaccurate. Consider using '#align set.smul_inter_ne_empty_iff Set.smul_inter_ne_empty_iffₓ'. -/
@[to_additive]
theorem smul_inter_ne_empty_iff {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x :=
  by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl⟩
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩
#align set.smul_inter_ne_empty_iff Set.smul_inter_ne_empty_iff
#align set.vadd_inter_ne_empty_iff Set.vadd_inter_ne_empty_iff

/- warning: set.smul_inter_ne_empty_iff' -> Set.smul_inter_ne_empty_iff' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (SMul.smul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (Mul.toSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a t) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b s)) (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toHasDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) x))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HSMul.hSMul.{u1, u1, u1} α (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} α (Set.{u1} α) (Set.smulSet.{u1, u1} α α (MulAction.toSMul.{u1, u1} α α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) (Monoid.toMulAction.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a t) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b s)) (Eq.{succ u1} α (HDiv.hDiv.{u1, u1, u1} α α α (instHDiv.{u1} α (DivInvMonoid.toDiv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))) a b) x))))
Case conversion may be inaccurate. Consider using '#align set.smul_inter_ne_empty_iff' Set.smul_inter_ne_empty_iff'ₓ'. -/
@[to_additive]
theorem smul_inter_ne_empty_iff' {s t : Set α} {x : α} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x := by
  simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]
#align set.smul_inter_ne_empty_iff' Set.smul_inter_ne_empty_iff'
#align set.vadd_inter_ne_empty_iff' Set.vadd_inter_ne_empty_iff'

/- warning: set.op_smul_inter_ne_empty_iff -> Set.op_smul_inter_ne_empty_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : MulOpposite.{u1} α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (SMul.smul.{u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.smulSet.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.hasEmptyc.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) a s) (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) b t)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) a) b) (MulOpposite.unop.{u1} α x)))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Group.{u1} α] {s : Set.{u1} α} {t : Set.{u1} α} {x : MulOpposite.{u1} α}, Iff (Ne.{succ u1} (Set.{u1} α) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (HSMul.hSMul.{u1, u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.{u1} α) (instHSMul.{u1, u1} (MulOpposite.{u1} α) (Set.{u1} α) (Set.smulSet.{u1, u1} (MulOpposite.{u1} α) α (Mul.toHasOppositeSMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))))) x s) t) (EmptyCollection.emptyCollection.{u1} (Set.{u1} α) (Set.instEmptyCollectionSet.{u1} α))) (Exists.{succ u1} α (fun (a : α) => Exists.{succ u1} α (fun (b : α) => And (And (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) a s) (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) b t)) (Eq.{succ u1} α (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) a) b) (MulOpposite.unop.{u1} α x)))))
Case conversion may be inaccurate. Consider using '#align set.op_smul_inter_ne_empty_iff Set.op_smul_inter_ne_empty_iffₓ'. -/
@[to_additive]
theorem op_smul_inter_ne_empty_iff {s t : Set α} {x : αᵐᵒᵖ} :
    x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = MulOpposite.unop x :=
  by
  rw [← nonempty_iff_ne_empty]
  constructor
  · rintro ⟨a, h, ha⟩
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩
  · rintro ⟨a, b, ⟨ha, hb⟩, H⟩
    have : MulOpposite.op (a⁻¹ * b) = x := congr_arg MulOpposite.op H
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩
#align set.op_smul_inter_ne_empty_iff Set.op_smul_inter_ne_empty_iff
#align set.op_vadd_inter_ne_empty_iff Set.op_vadd_inter_ne_empty_iff

/- warning: set.Union_inv_smul -> Set.unionᵢ_inv_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (g : α) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) g) s)) (Set.unionᵢ.{u2, succ u1} β α (fun (g : α) => SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2)) g s))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Group.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1))] {s : Set.{u2} β}, Eq.{succ u2} (Set.{u2} β) (Set.unionᵢ.{u2, succ u1} β α (fun (g : α) => HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) (Inv.inv.{u1} α (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (Group.toDivisionMonoid.{u1} α _inst_1)))) g) s)) (Set.unionᵢ.{u2, succ u1} β α (fun (g : α) => HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toSMul.{u1, u2} α β (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α _inst_1)) _inst_2))) g s))
Case conversion may be inaccurate. Consider using '#align set.Union_inv_smul Set.unionᵢ_inv_smulₓ'. -/
@[simp, to_additive]
theorem unionᵢ_inv_smul : (⋃ g : α, g⁻¹ • s) = ⋃ g : α, g • s :=
  Function.Surjective.supᵢ_congr _ inv_surjective fun g => rfl
#align set.Union_inv_smul Set.unionᵢ_inv_smul
#align set.Union_neg_vadd Set.unionᵢ_neg_vadd

#print Set.unionᵢ_smul_eq_setOf_exists /-
@[to_additive]
theorem unionᵢ_smul_eq_setOf_exists {s : Set β} : (⋃ g : α, g • s) = { a | ∃ g : α, g • a ∈ s } :=
  by simp_rw [← Union_set_of, ← Union_inv_smul, ← preimage_smul, preimage]
#align set.Union_smul_eq_set_of_exists Set.unionᵢ_smul_eq_setOf_exists
#align set.Union_vadd_eq_set_of_exists Set.unionᵢ_vadd_eq_setOf_exists
-/

end Group

section GroupWithZero

variable [GroupWithZero α] [MulAction α β] {s t : Set β} {a : α}

/- warning: set.smul_mem_smul_set_iff₀ -> Set.smul_mem_smul_set_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (A : Set.{u2} β) (x : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a x) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a A)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (A : Set.{u1} β) (x : β), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) a x) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a A)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x A))
Case conversion may be inaccurate. Consider using '#align set.smul_mem_smul_set_iff₀ Set.smul_mem_smul_set_iff₀ₓ'. -/
@[simp]
theorem smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : a • x ∈ a • A ↔ x ∈ A :=
  show Units.mk0 a ha • _ ∈ _ ↔ _ from smul_mem_smul_set_iff
#align set.smul_mem_smul_set_iff₀ Set.smul_mem_smul_set_iff₀

/- warning: set.mem_smul_set_iff_inv_smul_mem₀ -> Set.mem_smul_set_iff_inv_smul_mem₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (A : Set.{u2} β) (x : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a A)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) x) A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (A : Set.{u1} β) (x : β), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a A)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) x) A))
Case conversion may be inaccurate. Consider using '#align set.mem_smul_set_iff_inv_smul_mem₀ Set.mem_smul_set_iff_inv_smul_mem₀ₓ'. -/
theorem mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
  show _ ∈ Units.mk0 a ha • _ ↔ _ from mem_smul_set_iff_inv_smul_mem
#align set.mem_smul_set_iff_inv_smul_mem₀ Set.mem_smul_set_iff_inv_smul_mem₀

/- warning: set.mem_inv_smul_set_iff₀ -> Set.mem_inv_smul_set_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (A : Set.{u2} β) (x : β), Iff (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) x (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) A)) (Membership.Mem.{u2, u2} β (Set.{u2} β) (Set.hasMem.{u2} β) (SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a x) A))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (A : Set.{u1} β) (x : β), Iff (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) x (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) A)) (Membership.mem.{u1, u1} β (Set.{u1} β) (Set.instMembershipSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) a x) A))
Case conversion may be inaccurate. Consider using '#align set.mem_inv_smul_set_iff₀ Set.mem_inv_smul_set_iff₀ₓ'. -/
theorem mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : Set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
  show _ ∈ (Units.mk0 a ha)⁻¹ • _ ↔ _ from mem_inv_smul_set_iff
#align set.mem_inv_smul_set_iff₀ Set.mem_inv_smul_set_iff₀

/- warning: set.preimage_smul₀ -> Set.preimage_smul₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) a x) t) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u1} β β (fun (x : β) => HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) a x) t) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) t))
Case conversion may be inaccurate. Consider using '#align set.preimage_smul₀ Set.preimage_smul₀ₓ'. -/
theorem preimage_smul₀ (ha : a ≠ 0) (t : Set β) : (fun x => a • x) ⁻¹' t = a⁻¹ • t :=
  preimage_smul (Units.mk0 a ha) t
#align set.preimage_smul₀ Set.preimage_smul₀

/- warning: set.preimage_smul_inv₀ -> Set.preimage_smul_inv₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (Set.preimage.{u2, u2} β β (fun (x : β) => SMul.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) x) t) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a t))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall (t : Set.{u1} β), Eq.{succ u1} (Set.{u1} β) (Set.preimage.{u1, u1} β β (fun (x : β) => HSMul.hSMul.{u2, u1, u1} α β β (instHSMul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2)) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) x) t) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a t))
Case conversion may be inaccurate. Consider using '#align set.preimage_smul_inv₀ Set.preimage_smul_inv₀ₓ'. -/
theorem preimage_smul_inv₀ (ha : a ≠ 0) (t : Set β) : (fun x => a⁻¹ • x) ⁻¹' t = a • t :=
  preimage_smul (Units.mk0 a ha)⁻¹ t
#align set.preimage_smul_inv₀ Set.preimage_smul_inv₀

/- warning: set.set_smul_subset_set_smul_iff₀ -> Set.set_smul_subset_set_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {A : Set.{u2} β} {B : Set.{u2} β}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a A) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a B)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) A B))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall {A : Set.{u1} β} {B : Set.{u1} β}, Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a A) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a B)) (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) A B))
Case conversion may be inaccurate. Consider using '#align set.set_smul_subset_set_smul_iff₀ Set.set_smul_subset_set_smul_iff₀ₓ'. -/
@[simp]
theorem set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ a • B ↔ A ⊆ B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_set_smul_iff
#align set.set_smul_subset_set_smul_iff₀ Set.set_smul_subset_set_smul_iff₀

/- warning: set.set_smul_subset_iff₀ -> Set.set_smul_subset_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {A : Set.{u2} β} {B : Set.{u2} β}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a A) B) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) A (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) B)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall {A : Set.{u1} β} {B : Set.{u1} β}, Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a A) B) (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) A (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) B)))
Case conversion may be inaccurate. Consider using '#align set.set_smul_subset_iff₀ Set.set_smul_subset_iff₀ₓ'. -/
theorem set_smul_subset_iff₀ (ha : a ≠ 0) {A B : Set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
  show Units.mk0 a ha • _ ⊆ _ ↔ _ from set_smul_subset_iff
#align set.set_smul_subset_iff₀ Set.set_smul_subset_iff₀

/- warning: set.subset_set_smul_iff₀ -> Set.subset_set_smul_iff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (forall {A : Set.{u2} β} {B : Set.{u2} β}, Iff (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) A (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a B)) (HasSubset.Subset.{u2} (Set.{u2} β) (Set.hasSubset.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) (Inv.inv.{u1} α (DivInvMonoid.toHasInv.{u1} α (GroupWithZero.toDivInvMonoid.{u1} α _inst_1)) a) A) B))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (forall {A : Set.{u1} β} {B : Set.{u1} β}, Iff (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) A (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a B)) (HasSubset.Subset.{u1} (Set.{u1} β) (Set.instHasSubsetSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) (Inv.inv.{u2} α (GroupWithZero.toInv.{u2} α _inst_1) a) A) B))
Case conversion may be inaccurate. Consider using '#align set.subset_set_smul_iff₀ Set.subset_set_smul_iff₀ₓ'. -/
theorem subset_set_smul_iff₀ (ha : a ≠ 0) {A B : Set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
  show _ ⊆ Units.mk0 a ha • _ ↔ _ from subset_set_smul_iff
#align set.subset_set_smul_iff₀ Set.subset_set_smul_iff₀

/- warning: set.smul_set_inter₀ -> Set.smul_set_inter₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) s t)) (Inter.inter.{u2} (Set.{u2} β) (Set.hasInter.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {s : Set.{u1} β} {t : Set.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) s t)) (Inter.inter.{u1} (Set.{u1} β) (Set.instInterSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a t)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_inter₀ Set.smul_set_inter₀ₓ'. -/
theorem smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
  show Units.mk0 a ha • _ = _ from smul_set_inter
#align set.smul_set_inter₀ Set.smul_set_inter₀

/- warning: set.smul_set_sdiff₀ -> Set.smul_set_sdiff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s t)) (SDiff.sdiff.{u2} (Set.{u2} β) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {s : Set.{u1} β} {t : Set.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) s t)) (SDiff.sdiff.{u1} (Set.{u1} β) (Set.instSDiffSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a t)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_sdiff₀ Set.smul_set_sdiff₀ₓ'. -/
theorem smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
  image_diff (MulAction.injective₀ ha) _ _
#align set.smul_set_sdiff₀ Set.smul_set_sdiff₀

/- warning: set.smul_set_symm_diff₀ -> Set.smul_set_symm_diff₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {s : Set.{u2} β} {t : Set.{u2} β} {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) s t)) (symmDiff.{u2} (Set.{u2} β) (SemilatticeSup.toHasSup.{u2} (Set.{u2} β) (Lattice.toSemilatticeSup.{u2} (Set.{u2} β) (CompleteLattice.toLattice.{u2} (Set.{u2} β) (Order.Coframe.toCompleteLattice.{u2} (Set.{u2} β) (CompleteDistribLattice.toCoframe.{u2} (Set.{u2} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u2} (Set.{u2} β) (Set.completeBooleanAlgebra.{u2} β))))))) (BooleanAlgebra.toHasSdiff.{u2} (Set.{u2} β) (Set.booleanAlgebra.{u2} β)) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a s) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a t)))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {s : Set.{u1} β} {t : Set.{u1} β} {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a (symmDiff.{u1} (Set.{u1} β) (SemilatticeSup.toSup.{u1} (Set.{u1} β) (Lattice.toSemilatticeSup.{u1} (Set.{u1} β) (CompleteLattice.toLattice.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (Set.instSDiffSet.{u1} β) s t)) (symmDiff.{u1} (Set.{u1} β) (SemilatticeSup.toSup.{u1} (Set.{u1} β) (Lattice.toSemilatticeSup.{u1} (Set.{u1} β) (CompleteLattice.toLattice.{u1} (Set.{u1} β) (Order.Coframe.toCompleteLattice.{u1} (Set.{u1} β) (CompleteDistribLattice.toCoframe.{u1} (Set.{u1} β) (CompleteBooleanAlgebra.toCompleteDistribLattice.{u1} (Set.{u1} β) (Set.instCompleteBooleanAlgebraSet.{u1} β))))))) (Set.instSDiffSet.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a s) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a t)))
Case conversion may be inaccurate. Consider using '#align set.smul_set_symm_diff₀ Set.smul_set_symm_diff₀ₓ'. -/
theorem smul_set_symm_diff₀ (ha : a ≠ 0) : a • s ∆ t = (a • s) ∆ (a • t) :=
  image_symm_diff (MulAction.injective₀ ha) _ _
#align set.smul_set_symm_diff₀ Set.smul_set_symm_diff₀

/- warning: set.smul_set_univ₀ -> Set.smul_set_univ₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {a : α}, (Ne.{succ u1} α a (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) a (Set.univ.{u2} β)) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {a : α}, (Ne.{succ u2} α a (OfNat.ofNat.{u2} α 0 (Zero.toOfNat0.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} α (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} α (Set.{u1} β) (Set.smulSet.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) a (Set.univ.{u1} β)) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.smul_set_univ₀ Set.smul_set_univ₀ₓ'. -/
theorem smul_set_univ₀ (ha : a ≠ 0) : a • (univ : Set β) = univ :=
  image_univ_of_surjective <| MulAction.surjective₀ ha
#align set.smul_set_univ₀ Set.smul_set_univ₀

/- warning: set.smul_univ₀ -> Set.smul_univ₀ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α}, (Not (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s (OfNat.ofNat.{u1} (Set.{u1} α) 0 (OfNat.mk.{u1} (Set.{u1} α) 0 (Zero.zero.{u1} (Set.{u1} α) (Set.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)))))))))) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) s (Set.univ.{u2} β)) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {s : Set.{u2} α}, (Not (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s (OfNat.ofNat.{u2} (Set.{u2} α) 0 (Zero.toOfNat0.{u2} (Set.{u2} α) (Set.zero.{u2} α (MonoidWithZero.toZero.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))))))) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) s (Set.univ.{u1} β)) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.smul_univ₀ Set.smul_univ₀ₓ'. -/
theorem smul_univ₀ {s : Set α} (hs : ¬s ⊆ 0) : s • (univ : Set β) = univ :=
  let ⟨a, ha, ha₀⟩ := not_subset.1 hs
  eq_univ_of_forall fun b => ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩
#align set.smul_univ₀ Set.smul_univ₀

/- warning: set.smul_univ₀' -> Set.smul_univ₀' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : GroupWithZero.{u1} α] [_inst_2 : MulAction.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1))] {s : Set.{u1} α}, (Set.Nontrivial.{u1} α s) -> (Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (MulAction.toHasSmul.{u1, u2} α β (MonoidWithZero.toMonoid.{u1} α (GroupWithZero.toMonoidWithZero.{u1} α _inst_1)) _inst_2)) s (Set.univ.{u2} β)) (Set.univ.{u2} β))
but is expected to have type
  forall {α : Type.{u2}} {β : Type.{u1}} [_inst_1 : GroupWithZero.{u2} α] [_inst_2 : MulAction.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1))] {s : Set.{u2} α}, (Set.Nontrivial.{u2} α s) -> (Eq.{succ u1} (Set.{u1} β) (HSMul.hSMul.{u2, u1, u1} (Set.{u2} α) (Set.{u1} β) (Set.{u1} β) (instHSMul.{u2, u1} (Set.{u2} α) (Set.{u1} β) (Set.smul.{u2, u1} α β (MulAction.toSMul.{u2, u1} α β (MonoidWithZero.toMonoid.{u2} α (GroupWithZero.toMonoidWithZero.{u2} α _inst_1)) _inst_2))) s (Set.univ.{u1} β)) (Set.univ.{u1} β))
Case conversion may be inaccurate. Consider using '#align set.smul_univ₀' Set.smul_univ₀'ₓ'. -/
theorem smul_univ₀' {s : Set α} (hs : s.Nontrivial) : s • (univ : Set β) = univ :=
  smul_univ₀ hs.not_subset_singleton
#align set.smul_univ₀' Set.smul_univ₀'

end GroupWithZero

section Monoid

variable [Monoid α] [AddGroup β] [DistribMulAction α β] (a : α) (s : Set α) (t : Set β)

/- warning: set.smul_set_neg -> Set.smul_set_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) a (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) t)) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) a (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) t)) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) a t))
Case conversion may be inaccurate. Consider using '#align set.smul_set_neg Set.smul_set_negₓ'. -/
@[simp]
theorem smul_set_neg : a • -t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, smul_neg]
#align set.smul_set_neg Set.smul_set_neg

/- warning: set.smul_neg -> Set.smul_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) s (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) t)) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)))) (DistribSMul.toSmulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3)))) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Monoid.{u1} α] [_inst_2 : AddGroup.{u2} β] [_inst_3 : DistribMulAction.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) s (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) t)) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2))))) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (AddGroup.toSubtractionMonoid.{u2} β _inst_2)))) (DistribSMul.toSMulZeroClass.{u1, u2} α β (AddMonoid.toAddZeroClass.{u2} β (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2))) (DistribMulAction.toDistribSMul.{u1, u2} α β _inst_1 (SubNegMonoid.toAddMonoid.{u2} β (AddGroup.toSubNegMonoid.{u2} β _inst_2)) _inst_3))))) s t))
Case conversion may be inaccurate. Consider using '#align set.smul_neg Set.smul_negₓ'. -/
@[simp]
protected theorem smul_neg : s • -t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image_image2_right_comm smul_neg
#align set.smul_neg Set.smul_neg

end Monoid

section Ring

variable [Ring α] [AddCommGroup β] [Module α β] (a : α) (s : Set α) (t : Set β)

/- warning: set.neg_smul_set -> Set.neg_smul_set is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) (Neg.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))) a) t) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_2)))) (SMul.smul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) a t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] (a : α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) (Neg.neg.{u1} α (Ring.toNeg.{u1} α _inst_1) a) t) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2)))))) (HSMul.hSMul.{u1, u2, u2} α (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} α (Set.{u2} β) (Set.smulSet.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) a t))
Case conversion may be inaccurate. Consider using '#align set.neg_smul_set Set.neg_smul_setₓ'. -/
@[simp]
theorem neg_smul_set : -a • t = -(a • t) := by
  simp_rw [← image_smul, ← image_neg, image_image, neg_smul]
#align set.neg_smul_set Set.neg_smul_set

/- warning: set.neg_smul -> Set.neg_smul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) (Neg.neg.{u1} (Set.{u1} α) (Set.neg.{u1} α (SubNegMonoid.toHasNeg.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddGroupWithOne.toAddGroup.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))) s) t) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (SubNegMonoid.toHasNeg.{u2} β (AddGroup.toSubNegMonoid.{u2} β (AddCommGroup.toAddGroup.{u2} β _inst_2)))) (SMul.smul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toHasSmul.{u1, u2} α β (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} α β (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))))) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (AddZeroClass.toHasZero.{u2} β (AddMonoid.toAddZeroClass.{u2} β (AddCommMonoid.toAddMonoid.{u2} β (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3))))) s t))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : Ring.{u1} α] [_inst_2 : AddCommGroup.{u2} β] [_inst_3 : Module.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2)] (s : Set.{u1} α) (t : Set.{u2} β), Eq.{succ u2} (Set.{u2} β) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) (Neg.neg.{u1} (Set.{u1} α) (Set.neg.{u1} α (Ring.toNeg.{u1} α _inst_1)) s) t) (Neg.neg.{u2} (Set.{u2} β) (Set.neg.{u2} β (NegZeroClass.toNeg.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2)))))) (HSMul.hSMul.{u1, u2, u2} (Set.{u1} α) (Set.{u2} β) (Set.{u2} β) (instHSMul.{u1, u2} (Set.{u1} α) (Set.{u2} β) (Set.smul.{u1, u2} α β (SMulZeroClass.toSMul.{u1, u2} α β (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (SMulWithZero.toSMulZeroClass.{u1, u2} α β (MonoidWithZero.toZero.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1))) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (MulActionWithZero.toSMulWithZero.{u1, u2} α β (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α _inst_1)) (NegZeroClass.toZero.{u2} β (SubNegZeroMonoid.toNegZeroClass.{u2} β (SubtractionMonoid.toSubNegZeroMonoid.{u2} β (SubtractionCommMonoid.toSubtractionMonoid.{u2} β (AddCommGroup.toDivisionAddCommMonoid.{u2} β _inst_2))))) (Module.toMulActionWithZero.{u1, u2} α β (Ring.toSemiring.{u1} α _inst_1) (AddCommGroup.toAddCommMonoid.{u2} β _inst_2) _inst_3)))))) s t))
Case conversion may be inaccurate. Consider using '#align set.neg_smul Set.neg_smulₓ'. -/
@[simp]
protected theorem neg_smul : -s • t = -(s • t) :=
  by
  simp_rw [← image_neg]
  exact image2_image_left_comm neg_smul
#align set.neg_smul Set.neg_smul

end Ring

end Set

