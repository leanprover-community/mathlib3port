/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Order.ConditionallyCompleteLattice.Basic
import Data.Set.Finite

#align_import order.conditionally_complete_lattice.finset from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Conditionally complete lattices and finite sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


open Set

variable {α β γ : Type _}

section ConditionallyCompleteLattice

variable [ConditionallyCompleteLattice α] {s t : Set α} {a b : α}

/- warning: finset.nonempty.sup'_eq_cSup_image clashes with finset.sup'_eq_cSup_image -> Finset.sup'_eq_csSup_image
Case conversion may be inaccurate. Consider using '#align finset.nonempty.sup'_eq_cSup_image Finset.sup'_eq_csSup_imageₓ'. -/
#print Finset.sup'_eq_csSup_image /-
theorem Finset.sup'_eq_csSup_image {s : Finset β} (hs : s.Nonempty) (f : β → α) :
    s.sup' hs f = sSup (f '' s) :=
  eq_of_forall_ge_iff fun a => by
    simp [csSup_le_iff (s.finite_to_set.image f).BddAbove (hs.to_set.image f)]
#align finset.nonempty.sup'_eq_cSup_image Finset.sup'_eq_csSup_image
-/

/- warning: finset.nonempty.sup'_id_eq_cSup clashes with finset.sup'_id_eq_cSup -> Finset.sup'_id_eq_csSup
Case conversion may be inaccurate. Consider using '#align finset.nonempty.sup'_id_eq_cSup Finset.sup'_id_eq_csSupₓ'. -/
#print Finset.sup'_id_eq_csSup /-
theorem Finset.sup'_id_eq_csSup {s : Finset α} (hs : s.Nonempty) : s.sup' hs id = sSup s := by
  rw [hs.sup'_eq_cSup_image, image_id]
#align finset.nonempty.sup'_id_eq_cSup Finset.sup'_id_eq_csSup
-/

end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder

variable [ConditionallyCompleteLinearOrder α] {s t : Set α} {a b : α}

#print Finset.Nonempty.csSup_eq_max' /-
theorem Finset.Nonempty.csSup_eq_max' {s : Finset α} (h : s.Nonempty) : sSup ↑s = s.max' h :=
  eq_of_forall_ge_iff fun a => (csSup_le_iff s.BddAbove h.to_set).trans (s.max'_le_iff h).symm
#align finset.nonempty.cSup_eq_max' Finset.Nonempty.csSup_eq_max'
-/

#print Finset.Nonempty.csInf_eq_min' /-
theorem Finset.Nonempty.csInf_eq_min' {s : Finset α} (h : s.Nonempty) : sInf ↑s = s.min' h :=
  @Finset.Nonempty.csSup_eq_max' αᵒᵈ _ s h
#align finset.nonempty.cInf_eq_min' Finset.Nonempty.csInf_eq_min'
-/

#print Finset.Nonempty.csSup_mem /-
theorem Finset.Nonempty.csSup_mem {s : Finset α} (h : s.Nonempty) : sSup (s : Set α) ∈ s := by
  rw [h.cSup_eq_max']; exact s.max'_mem _
#align finset.nonempty.cSup_mem Finset.Nonempty.csSup_mem
-/

#print Finset.Nonempty.csInf_mem /-
theorem Finset.Nonempty.csInf_mem {s : Finset α} (h : s.Nonempty) : sInf (s : Set α) ∈ s :=
  @Finset.Nonempty.csSup_mem αᵒᵈ _ _ h
#align finset.nonempty.cInf_mem Finset.Nonempty.csInf_mem
-/

#print Set.Nonempty.csSup_mem /-
theorem Set.Nonempty.csSup_mem (h : s.Nonempty) (hs : s.Finite) : sSup s ∈ s := by
  lift s to Finset α using hs; exact Finset.Nonempty.csSup_mem h
#align set.nonempty.cSup_mem Set.Nonempty.csSup_mem
-/

#print Set.Nonempty.csInf_mem /-
theorem Set.Nonempty.csInf_mem (h : s.Nonempty) (hs : s.Finite) : sInf s ∈ s :=
  @Set.Nonempty.csSup_mem αᵒᵈ _ _ h hs
#align set.nonempty.cInf_mem Set.Nonempty.csInf_mem
-/

#print Set.Finite.csSup_lt_iff /-
theorem Set.Finite.csSup_lt_iff (hs : s.Finite) (h : s.Nonempty) : sSup s < a ↔ ∀ x ∈ s, x < a :=
  ⟨fun h x hx => (le_csSup hs.BddAbove hx).trans_lt h, fun H => H _ <| h.csSup_mem hs⟩
#align set.finite.cSup_lt_iff Set.Finite.csSup_lt_iff
-/

#print Set.Finite.lt_csInf_iff /-
theorem Set.Finite.lt_csInf_iff (hs : s.Finite) (h : s.Nonempty) : a < sInf s ↔ ∀ x ∈ s, a < x :=
  @Set.Finite.csSup_lt_iff αᵒᵈ _ _ _ hs h
#align set.finite.lt_cInf_iff Set.Finite.lt_csInf_iff
-/

end ConditionallyCompleteLinearOrder

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/


namespace Finset

#print Finset.sup'_eq_csSup_image /-
theorem sup'_eq_csSup_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.sup' H f = sSup (f '' s) := by
  apply le_antisymm
  · refine' Finset.sup'_le _ _ fun a ha => _
    refine' le_csSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩
    rintro i ⟨j, hj, rfl⟩
    exact Finset.le_sup' _ hj
  · apply csSup_le ((coe_nonempty.mpr H).image _)
    rintro _ ⟨a, ha, rfl⟩
    exact Finset.le_sup' _ ha
#align finset.sup'_eq_cSup_image Finset.sup'_eq_csSup_image
-/

#print Finset.inf'_eq_csInf_image /-
theorem inf'_eq_csInf_image [ConditionallyCompleteLattice β] (s : Finset α) (H) (f : α → β) :
    s.inf' H f = sInf (f '' s) :=
  @sup'_eq_csSup_image _ βᵒᵈ _ _ H _
#align finset.inf'_eq_cInf_image Finset.inf'_eq_csInf_image
-/

#print Finset.sup'_id_eq_csSup /-
theorem sup'_id_eq_csSup [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.sup' H id = sSup s := by rw [sup'_eq_cSup_image s H, Set.image_id]
#align finset.sup'_id_eq_cSup Finset.sup'_id_eq_csSup
-/

#print Finset.inf'_id_eq_csInf /-
theorem inf'_id_eq_csInf [ConditionallyCompleteLattice α] (s : Finset α) (H) :
    s.inf' H id = sInf s :=
  @sup'_id_eq_csSup αᵒᵈ _ _ H
#align finset.inf'_id_eq_cInf Finset.inf'_id_eq_csInf
-/

end Finset

