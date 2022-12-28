/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ring_hom.finite_type
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.LocalProperties
import Mathbin.RingTheory.Localization.InvSubmonoid

/-!

# The meta properties of finite-type ring homomorphisms.

The main result is `ring_hom.finite_is_local`.

-/


namespace RingHom

open Pointwise

theorem finite_type_stable_under_composition : StableUnderComposition @FiniteType :=
  by
  introv R hf hg
  exact hg.comp hf
#align ring_hom.finite_type_stable_under_composition RingHom.finite_type_stable_under_composition

theorem finite_type_holds_for_localization_away : HoldsForLocalizationAway @FiniteType :=
  by
  introv R _
  skip
  suffices Algebra.FiniteType R S by
    change Algebra.FiniteType _ _
    convert this
    ext
    rw [Algebra.smul_def]
    rfl
  exact IsLocalization.finite_type_of_monoid_fg (Submonoid.powers r) S
#align
  ring_hom.finite_type_holds_for_localization_away RingHom.finite_type_holds_for_localization_away

theorem finite_type_of_localization_span_target : OfLocalizationSpanTarget @FiniteType :=
  by
  -- Setup algebra intances.
  rw [of_localization_span_target_iff_finite]
  introv R hs H
  skip
  classical
    letI := f.to_algebra
    replace H : ∀ r : s, Algebra.FiniteType R (Localization.Away (r : S))
    · intro r
      convert H r
      ext
      rw [Algebra.smul_def]
      rfl
    replace H := fun r => (H r).1
    constructor
    -- Suppose `s : finset S` spans `S`, and each `Sᵣ` is finitely generated as an `R`-algebra.
    -- Say `t r : finset Sᵣ` generates `Sᵣ`. By assumption, we may find `lᵢ` such that
    -- `∑ lᵢ * sᵢ = 1`. I claim that all `s` and `l` and the numerators of `t` and generates `S`.
    choose t ht using H
    obtain ⟨l, hl⟩ :=
      (Finsupp.mem_span_iff_total S (s : Set S) 1).mp
        (show (1 : S) ∈ Ideal.span (s : Set S) by
          rw [hs]
          trivial)
    let sf := fun x : s => IsLocalization.finsetIntegerMultiple (Submonoid.powers (x : S)) (t x)
    use s.attach.bUnion sf ∪ s ∪ l.support.image l
    rw [eq_top_iff]
    -- We need to show that every `x` falls in the subalgebra generated by those elements.
    -- Since all `s` and `l` are in the subalgebra, it suffices to check that `sᵢ ^ nᵢ • x` falls in
    -- the algebra for each `sᵢ` and some `nᵢ`.
    rintro x -
    apply Subalgebra.mem_of_span_eq_top_of_smul_pow_mem _ (s : Set S) l hl _ _ x _
    · intro x hx
      apply Algebra.subset_adjoin
      rw [Finset.coe_union, Finset.coe_union]
      exact Or.inl (Or.inr hx)
    · intro i
      by_cases h : l i = 0
      · rw [h]
        exact zero_mem _
      apply Algebra.subset_adjoin
      rw [Finset.coe_union, Finset.coe_image]
      exact Or.inr (Set.mem_image_of_mem _ (finsupp.mem_support_iff.mpr h))
    · intro r
      rw [Finset.coe_union, Finset.coe_union, Finset.coe_bUnion]
      -- Since all `sᵢ` and numerators of `t r` are in the algebra, it suffices to show that the
      -- image of `x` in `Sᵣ` falls in the `R`-adjoin of `t r`, which is of course true.
      obtain ⟨⟨_, n₂, rfl⟩, hn₂⟩ :=
        IsLocalization.exists_smul_mem_of_mem_adjoin (Submonoid.powers (r : S)) x (t r)
          (Algebra.adjoin R _) _ _ _
      · exact ⟨n₂, hn₂⟩
      · intro x hx
        apply Algebra.subset_adjoin
        refine' Or.inl (Or.inl ⟨_, ⟨r, rfl⟩, _, ⟨s.mem_attach r, rfl⟩, hx⟩)
      · rw [Submonoid.powers_eq_closure, Submonoid.closure_le, Set.singleton_subset_iff]
        apply Algebra.subset_adjoin
        exact Or.inl (Or.inr r.2)
      · rw [ht]
        trivial
#align
  ring_hom.finite_type_of_localization_span_target RingHom.finite_type_of_localization_span_target

theorem finite_type_is_local : PropertyIsLocal @FiniteType :=
  ⟨localization_finite_type, finite_type_of_localization_span_target,
    finite_type_stable_under_composition, finite_type_holds_for_localization_away⟩
#align ring_hom.finite_type_is_local RingHom.finite_type_is_local

theorem finite_type_respects_iso : RingHom.RespectsIso @RingHom.FiniteType :=
  RingHom.finite_type_is_local.RespectsIso
#align ring_hom.finite_type_respects_iso RingHom.finite_type_respects_iso

end RingHom

