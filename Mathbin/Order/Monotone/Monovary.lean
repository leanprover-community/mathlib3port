/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module order.monotone.monovary
! leanprover-community/mathlib commit baba818b9acea366489e8ba32d2cc0fcaf50a1f7
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Image

/-!
# Monovariance of functions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `algebra.order.rearrangement`.

## Main declarations

* `monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `monovary_on f g s`: `f` monovaries with `g` on `s`.
* `monovary_on f g s`: `f` antivaries with `g` on `s`.
-/


open Function Set

variable {ι ι' α β γ : Type _}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s t : Set ι}

#print Monovary /-
/-- `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j
#align monovary Monovary
-/

#print Antivary /-
/-- `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i
#align antivary Antivary
-/

#print MonovaryOn /-
/-- `f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j ∈ s`. -/
def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (hi : i ∈ s) ⦃j⦄ (hj : j ∈ s), g i < g j → f i ≤ f j
#align monovary_on MonovaryOn
-/

#print AntivaryOn /-
/-- `f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j ∈ s`. -/
def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (hi : i ∈ s) ⦃j⦄ (hj : j ∈ s), g i < g j → f j ≤ f i
#align antivary_on AntivaryOn
-/

#print Monovary.monovaryOn /-
protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun i _ j _ hij => h hij
#align monovary.monovary_on Monovary.monovaryOn
-/

#print Antivary.antivaryOn /-
protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun i _ j _ hij => h hij
#align antivary.antivary_on Antivary.antivaryOn
-/

#print MonovaryOn.empty /-
@[simp]
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun i => False.elim
#align monovary_on.empty MonovaryOn.empty
-/

#print AntivaryOn.empty /-
@[simp]
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun i => False.elim
#align antivary_on.empty AntivaryOn.empty
-/

#print monovaryOn_univ /-
@[simp]
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h i j => h trivial trivial, fun h i _ j _ hij => h hij⟩
#align monovary_on_univ monovaryOn_univ
-/

#print antivaryOn_univ /-
@[simp]
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h i j => h trivial trivial, fun h i _ j _ hij => h hij⟩
#align antivary_on_univ antivaryOn_univ
-/

#print MonovaryOn.subset /-
protected theorem MonovaryOn.subset (hst : s ⊆ t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun i hi j hj => h (hst hi) (hst hj)
#align monovary_on.subset MonovaryOn.subset
-/

#print AntivaryOn.subset /-
protected theorem AntivaryOn.subset (hst : s ⊆ t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun i hi j hj => h (hst hi) (hst hj)
#align antivary_on.subset AntivaryOn.subset
-/

#print monovary_const_left /-
theorem monovary_const_left (g : ι → β) (a : α) : Monovary (const ι a) g := fun i j _ => le_rfl
#align monovary_const_left monovary_const_left
-/

#print antivary_const_left /-
theorem antivary_const_left (g : ι → β) (a : α) : Antivary (const ι a) g := fun i j _ => le_rfl
#align antivary_const_left antivary_const_left
-/

#print monovary_const_right /-
theorem monovary_const_right (f : ι → α) (b : β) : Monovary f (const ι b) := fun i j h =>
  (h.Ne rfl).elim
#align monovary_const_right monovary_const_right
-/

#print antivary_const_right /-
theorem antivary_const_right (f : ι → α) (b : β) : Antivary f (const ι b) := fun i j h =>
  (h.Ne rfl).elim
#align antivary_const_right antivary_const_right
-/

#print monovary_self /-
theorem monovary_self (f : ι → α) : Monovary f f := fun i j => le_of_lt
#align monovary_self monovary_self
-/

#print monovaryOn_self /-
theorem monovaryOn_self (f : ι → α) (s : Set ι) : MonovaryOn f f s := fun i _ j _ => le_of_lt
#align monovary_on_self monovaryOn_self
-/

#print Subsingleton.monovary /-
protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι → α) (g : ι → β) : Monovary f g :=
  fun i j h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary Subsingleton.monovary
-/

#print Subsingleton.antivary /-
protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι → α) (g : ι → β) : Antivary f g :=
  fun i j h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary Subsingleton.antivary
-/

#print Subsingleton.monovaryOn /-
protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    MonovaryOn f g s := fun i _ j _ h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary_on Subsingleton.monovaryOn
-/

#print Subsingleton.antivaryOn /-
protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    AntivaryOn f g s := fun i _ j _ h => (ne_of_apply_ne _ h.Ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary_on Subsingleton.antivaryOn
-/

#print monovaryOn_const_left /-
theorem monovaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun i _ j _ _ => le_rfl
#align monovary_on_const_left monovaryOn_const_left
-/

#print antivaryOn_const_left /-
theorem antivaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun i _ j _ _ => le_rfl
#align antivary_on_const_left antivaryOn_const_left
-/

#print monovaryOn_const_right /-
theorem monovaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun i _ j _ h => (h.Ne rfl).elim
#align monovary_on_const_right monovaryOn_const_right
-/

#print antivaryOn_const_right /-
theorem antivaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun i _ j _ h => (h.Ne rfl).elim
#align antivary_on_const_right antivaryOn_const_right
-/

#print Monovary.comp_right /-
theorem Monovary.comp_right (h : Monovary f g) (k : ι' → ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun i j hij => h hij
#align monovary.comp_right Monovary.comp_right
-/

#print Antivary.comp_right /-
theorem Antivary.comp_right (h : Antivary f g) (k : ι' → ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun i j hij => h hij
#align antivary.comp_right Antivary.comp_right
-/

#print MonovaryOn.comp_right /-
theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' → ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun i hi j hj => h hi hj
#align monovary_on.comp_right MonovaryOn.comp_right
-/

#print AntivaryOn.comp_right /-
theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' → ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun i hi j hj => h hi hj
#align antivary_on.comp_right AntivaryOn.comp_right
-/

#print Monovary.comp_monotone_left /-
theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align monovary.comp_monotone_left Monovary.comp_monotone_left
-/

#print Monovary.comp_antitone_left /-
theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align monovary.comp_antitone_left Monovary.comp_antitone_left
-/

#print Antivary.comp_monotone_left /-
theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align antivary.comp_monotone_left Antivary.comp_monotone_left
-/

#print Antivary.comp_antitone_left /-
theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
  fun i j hij => hf <| h hij
#align antivary.comp_antitone_left Antivary.comp_antitone_left
-/

#print MonovaryOn.comp_monotone_on_left /-
theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
    MonovaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align monovary_on.comp_monotone_on_left MonovaryOn.comp_monotone_on_left
-/

#print MonovaryOn.comp_antitone_on_left /-
theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
    AntivaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align monovary_on.comp_antitone_on_left MonovaryOn.comp_antitone_on_left
-/

#print AntivaryOn.comp_monotone_on_left /-
theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
    AntivaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align antivary_on.comp_monotone_on_left AntivaryOn.comp_monotone_on_left
-/

#print AntivaryOn.comp_antitone_on_left /-
theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
    MonovaryOn (f' ∘ f) g s := fun i hi j hj hij => hf <| h hi hj hij
#align antivary_on.comp_antitone_on_left AntivaryOn.comp_antitone_on_left
-/

section OrderDual

open OrderDual

#print Monovary.dual /-
theorem Monovary.dual : Monovary f g → Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align monovary.dual Monovary.dual
-/

#print Antivary.dual /-
theorem Antivary.dual : Antivary f g → Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align antivary.dual Antivary.dual
-/

#print Monovary.dual_left /-
theorem Monovary.dual_left : Monovary f g → Antivary (toDual ∘ f) g :=
  id
#align monovary.dual_left Monovary.dual_left
-/

#print Antivary.dual_left /-
theorem Antivary.dual_left : Antivary f g → Monovary (toDual ∘ f) g :=
  id
#align antivary.dual_left Antivary.dual_left
-/

#print Monovary.dual_right /-
theorem Monovary.dual_right : Monovary f g → Antivary f (toDual ∘ g) :=
  swap
#align monovary.dual_right Monovary.dual_right
-/

#print Antivary.dual_right /-
theorem Antivary.dual_right : Antivary f g → Monovary f (toDual ∘ g) :=
  swap
#align antivary.dual_right Antivary.dual_right
-/

#print MonovaryOn.dual /-
theorem MonovaryOn.dual : MonovaryOn f g s → MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual MonovaryOn.dual
-/

#print AntivaryOn.dual /-
theorem AntivaryOn.dual : AntivaryOn f g s → AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual AntivaryOn.dual
-/

#print MonovaryOn.dual_left /-
theorem MonovaryOn.dual_left : MonovaryOn f g s → AntivaryOn (toDual ∘ f) g s :=
  id
#align monovary_on.dual_left MonovaryOn.dual_left
-/

#print AntivaryOn.dual_left /-
theorem AntivaryOn.dual_left : AntivaryOn f g s → MonovaryOn (toDual ∘ f) g s :=
  id
#align antivary_on.dual_left AntivaryOn.dual_left
-/

#print MonovaryOn.dual_right /-
theorem MonovaryOn.dual_right : MonovaryOn f g s → AntivaryOn f (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual_right MonovaryOn.dual_right
-/

#print AntivaryOn.dual_right /-
theorem AntivaryOn.dual_right : AntivaryOn f g s → MonovaryOn f (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual_right AntivaryOn.dual_right
-/

#print monovary_toDual_left /-
@[simp]
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl
#align monovary_to_dual_left monovary_toDual_left
-/

#print monovary_toDual_right /-
@[simp]
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_swap
#align monovary_to_dual_right monovary_toDual_right
-/

#print antivary_toDual_left /-
@[simp]
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl
#align antivary_to_dual_left antivary_toDual_left
-/

#print antivary_toDual_right /-
@[simp]
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_swap
#align antivary_to_dual_right antivary_toDual_right
-/

#print monovaryOn_toDual_left /-
@[simp]
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl
#align monovary_on_to_dual_left monovaryOn_toDual_left
-/

#print monovaryOn_toDual_right /-
@[simp]
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_swap
#align monovary_on_to_dual_right monovaryOn_toDual_right
-/

#print antivaryOn_toDual_left /-
@[simp]
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl
#align antivary_on_to_dual_left antivaryOn_toDual_left
-/

#print antivaryOn_toDual_right /-
@[simp]
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_swap
#align antivary_on_to_dual_right antivaryOn_toDual_right
-/

end OrderDual

section PartialOrder

variable [PartialOrder ι]

#print monovary_id_iff /-
@[simp]
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm
#align monovary_id_iff monovary_id_iff
-/

#print antivary_id_iff /-
@[simp]
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm
#align antivary_id_iff antivary_id_iff
-/

#print monovaryOn_id_iff /-
@[simp]
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm
#align monovary_on_id_iff monovaryOn_id_iff
-/

#print antivaryOn_id_iff /-
@[simp]
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm
#align antivary_on_id_iff antivaryOn_id_iff
-/

end PartialOrder

variable [LinearOrder ι]

#print Monotone.monovary /-
protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun i j hij => hf (hg.reflect_lt hij).le
#align monotone.monovary Monotone.monovary
-/

#print Monotone.antivary /-
protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.Monovary hg.dual_right).dual_right
#align monotone.antivary Monotone.antivary
-/

#print Antitone.monovary /-
protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.Antivary hg).dual_left
#align antitone.monovary Antitone.monovary
-/

#print Antitone.antivary /-
protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.Monovary hg.dual_right).dual_right
#align antitone.antivary Antitone.antivary
-/

#print MonotoneOn.monovaryOn /-
protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun i hi j hj hij => hf hi hj (hg.reflect_lt hi hj hij).le
#align monotone_on.monovary_on MonotoneOn.monovaryOn
-/

#print MonotoneOn.antivaryOn /-
protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.MonovaryOn hg.dual_right).dual_right
#align monotone_on.antivary_on MonotoneOn.antivaryOn
-/

#print AntitoneOn.monovaryOn /-
protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.AntivaryOn hg).dual_left
#align antitone_on.monovary_on AntitoneOn.monovaryOn
-/

#print AntitoneOn.antivaryOn /-
protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.MonovaryOn hg.dual_right).dual_right
#align antitone_on.antivary_on AntitoneOn.antivaryOn
-/

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s : Set ι}

#print MonovaryOn.comp_monotoneOn_right /-
theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_monotone_on_right MonovaryOn.comp_monotoneOn_right
-/

#print MonovaryOn.comp_antitoneOn_right /-
theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_antitone_on_right MonovaryOn.comp_antitoneOn_right
-/

#print AntivaryOn.comp_monotoneOn_right /-
theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_monotone_on_right AntivaryOn.comp_monotoneOn_right
-/

#print AntivaryOn.comp_antitoneOn_right /-
theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun i hi j hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_antitone_on_right AntivaryOn.comp_antitoneOn_right
-/

#print Monovary.symm /-
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun i j hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align monovary.symm Monovary.symm
-/

#print Antivary.symm /-
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun i j hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align antivary.symm Antivary.symm
-/

#print MonovaryOn.symm /-
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun i hi j hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hj hi hg
#align monovary_on.symm MonovaryOn.symm
-/

#print AntivaryOn.symm /-
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun i hi j hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hi hj hg
#align antivary_on.symm AntivaryOn.symm
-/

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι → α} {g : ι → β} {s : Set ι}

#print monovary_comm /-
protected theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩
#align monovary_comm monovary_comm
-/

#print antivary_comm /-
protected theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩
#align antivary_comm antivary_comm
-/

#print monovaryOn_comm /-
protected theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩
#align monovary_on_comm monovaryOn_comm
-/

#print antivaryOn_comm /-
protected theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩
#align antivary_on_comm antivaryOn_comm
-/

end LinearOrder

