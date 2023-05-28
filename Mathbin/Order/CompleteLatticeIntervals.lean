/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module order.complete_lattice_intervals
! leanprover-community/mathlib commit c3291da49cfa65f0d43b094750541c0731edc932
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Basic
import Mathbin.Data.Set.Intervals.OrdConnected

/-! # Subtypes of conditionally complete linear orders

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

## TODO

Add appropriate instances for all `set.Ixx`. This requires a refactor that will allow different
default values for `Sup` and `Inf`.
-/


open Classical

open Set

variable {α : Type _} (s : Set α)

section SupSet

variable [SupSet α]

#print subsetSupSet /-
/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetSupSet [Inhabited s] : SupSet s
    where sSup t :=
    if ht : sSup (coe '' t : Set α) ∈ s then ⟨sSup (coe '' t : Set α), ht⟩ else default
#align subset_has_Sup subsetSupSet
-/

attribute [local instance] subsetSupSet

#print subset_sSup_def /-
@[simp]
theorem subset_sSup_def [Inhabited s] :
    @sSup s _ = fun t =>
      if ht : sSup (coe '' t : Set α) ∈ s then ⟨sSup (coe '' t : Set α), ht⟩ else default :=
  rfl
#align subset_Sup_def subset_sSup_def
-/

#print subset_sSup_of_within /-
theorem subset_sSup_of_within [Inhabited s] {t : Set s} (h : sSup (coe '' t : Set α) ∈ s) :
    sSup (coe '' t : Set α) = (@sSup s _ t : α) := by simp [dif_pos h]
#align subset_Sup_of_within subset_sSup_of_within
-/

end SupSet

section InfSet

variable [InfSet α]

#print subsetInfSet /-
/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetInfSet [Inhabited s] : InfSet s
    where sInf t :=
    if ht : sInf (coe '' t : Set α) ∈ s then ⟨sInf (coe '' t : Set α), ht⟩ else default
#align subset_has_Inf subsetInfSet
-/

attribute [local instance] subsetInfSet

#print subset_sInf_def /-
@[simp]
theorem subset_sInf_def [Inhabited s] :
    @sInf s _ = fun t =>
      if ht : sInf (coe '' t : Set α) ∈ s then ⟨sInf (coe '' t : Set α), ht⟩ else default :=
  rfl
#align subset_Inf_def subset_sInf_def
-/

#print subset_sInf_of_within /-
theorem subset_sInf_of_within [Inhabited s] {t : Set s} (h : sInf (coe '' t : Set α) ∈ s) :
    sInf (coe '' t : Set α) = (@sInf s _ t : α) := by simp [dif_pos h]
#align subset_Inf_of_within subset_sInf_of_within
-/

end InfSet

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetSupSet

attribute [local instance] subsetInfSet

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddAbove t), sSup (coe '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddBelow t), sInf (coe '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  {-- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
      subsetSupSet
      s,
    subsetInfSet s, DistribLattice.toLattice s,
    (inferInstance :
      LinearOrder
        s) with
    le_cSup := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).le_csSup_image hct h_bdd
      rwa [subset_sSup_of_within s (h_Sup ⟨c, hct⟩ h_bdd)] at this
    cSup_le := by
      rintro t B ht hB
      have := (Subtype.mono_coe s).csSup_image_le ht hB
      rwa [subset_sSup_of_within s (h_Sup ht ⟨B, hB⟩)] at this
    le_cInf := by
      intro t B ht hB
      have := (Subtype.mono_coe s).le_csInf_image ht hB
      rwa [subset_sInf_of_within s (h_Inf ht ⟨B, hB⟩)] at this
    cInf_le := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).csInf_image_le hct h_bdd
      rwa [subset_sInf_of_within s (h_Inf ⟨c, hct⟩ h_bdd)] at this }
#align subset_conditionally_complete_linear_order subsetConditionallyCompleteLinearOrder

section OrdConnected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem sSup_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sSup (coe '' t : Set α) ∈ s :=
  by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ upperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_csSup_image hct ⟨B, hB⟩
  · exact (Subtype.mono_coe s).csSup_image_le ⟨c, hct⟩ hB
#align Sup_within_of_ord_connected sSup_within_of_ordConnected

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem sInf_within_of_ordConnected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : sInf (coe '' t : Set α) ∈ s :=
  by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ lowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_csInf_image ⟨c, hct⟩ hB
  · exact (Subtype.mono_coe s).csInf_image_le hct ⟨B, hB⟩
#align Inf_within_of_ord_connected sInf_within_of_ordConnected

#print ordConnectedSubsetConditionallyCompleteLinearOrder /-
/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s]
    [OrdConnected s] : ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s sSup_within_of_ordConnected sInf_within_of_ordConnected
#align ord_connected_subset_conditionally_complete_linear_order ordConnectedSubsetConditionallyCompleteLinearOrder
-/

end OrdConnected

