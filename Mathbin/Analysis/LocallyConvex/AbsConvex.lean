/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll

! This file was ported from Lean 3 source module analysis.locally_convex.abs_convex
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.LocallyConvex.BalancedCoreHull
import Mathbin.Analysis.LocallyConvex.WithSeminorms
import Mathbin.Analysis.Convex.Gauge

/-!
# Absolutely convex sets

A set is called absolutely convex or disked if it is convex and balanced.
The importance of absolutely convex sets comes from the fact that every locally convex
topological vector space has a basis consisting of absolutely convex sets.

## Main definitions

* `gauge_seminorm_family`: the seminorm family induced by all open absolutely convex neighborhoods
of zero.

## Main statements

* `with_gauge_seminorm_family`: the topology of a locally convex space is induced by the family
`gauge_seminorm_family`.

## Todo

* Define the disked hull

## Tags

disks, convex, balanced
-/


open NormedField Set

open BigOperators Nnreal Pointwise TopologicalSpace

variable {𝕜 E F G ι : Type _}

section NontriviallyNormedField

variable (𝕜 E) {s : Set E}

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]

variable [Module ℝ E] [SMulCommClass ℝ 𝕜 E]

variable [TopologicalSpace E] [LocallyConvexSpace ℝ E] [HasContinuousSmul 𝕜 E]

theorem nhds_basis_abs_convex :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => s ∈ 𝓝 (0 : E) ∧ Balanced 𝕜 s ∧ Convex ℝ s) id := by
  refine'
    (LocallyConvexSpace.convex_basis_zero ℝ E).to_has_basis (fun s hs => _) fun s hs =>
      ⟨s, ⟨hs.1, hs.2.2⟩, rfl.subset⟩
  refine' ⟨convexHull ℝ (balancedCore 𝕜 s), _, convex_hull_min (balanced_core_subset s) hs.2⟩
  refine' ⟨Filter.mem_of_superset (balanced_core_mem_nhds_zero hs.1) (subset_convex_hull ℝ _), _⟩
  refine' ⟨balancedConvexHullOfBalanced (balancedCoreBalanced s), _⟩
  exact convex_convex_hull ℝ (balancedCore 𝕜 s)
#align nhds_basis_abs_convex nhds_basis_abs_convex

variable [HasContinuousSmul ℝ E] [TopologicalAddGroup E]

theorem nhds_basis_abs_convex_open :
    (𝓝 (0 : E)).HasBasis (fun s : Set E => (0 : E) ∈ s ∧ IsOpen s ∧ Balanced 𝕜 s ∧ Convex ℝ s) id :=
  by 
  refine' (nhds_basis_abs_convex 𝕜 E).to_has_basis _ _
  · rintro s ⟨hs_nhds, hs_balanced, hs_convex⟩
    refine' ⟨interior s, _, interior_subset⟩
    exact
      ⟨mem_interior_iff_mem_nhds.mpr hs_nhds, is_open_interior,
        hs_balanced.interior (mem_interior_iff_mem_nhds.mpr hs_nhds), hs_convex.interior⟩
  rintro s ⟨hs_zero, hs_open, hs_balanced, hs_convex⟩
  exact ⟨s, ⟨hs_open.mem_nhds hs_zero, hs_balanced, hs_convex⟩, rfl.subset⟩
#align nhds_basis_abs_convex_open nhds_basis_abs_convex_open

end NontriviallyNormedField

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [Zero E] [SemiNormedRing 𝕜]

variable [HasSmul 𝕜 E] [HasSmul ℝ E]

variable (𝕜 E)

/-- The type of absolutely convex open sets. -/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) ∈ s ∧ IsOpen s ∧ Balanced 𝕜 s ∧ Convex ℝ s }
#align abs_convex_open_sets AbsConvexOpenSets

instance AbsConvexOpenSets.hasCoe : Coe (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩
#align abs_convex_open_sets.has_coe AbsConvexOpenSets.hasCoe

namespace AbsConvexOpenSets

variable {𝕜 E}

theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) ∈ (s : Set E) :=
  s.2.1
#align abs_convex_open_sets.coe_zero_mem AbsConvexOpenSets.coe_zero_mem

theorem coe_is_open (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1
#align abs_convex_open_sets.coe_is_open AbsConvexOpenSets.coe_is_open

theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) ∈ 𝓝 (0 : E) :=
  s.coe_is_open.mem_nhds s.coe_zero_mem
#align abs_convex_open_sets.coe_nhds AbsConvexOpenSets.coe_nhds

theorem coeBalanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1
#align abs_convex_open_sets.coe_balanced AbsConvexOpenSets.coeBalanced

theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex ℝ (s : Set E) :=
  s.2.2.2.2
#align abs_convex_open_sets.coe_convex AbsConvexOpenSets.coe_convex

end AbsConvexOpenSets

instance : Nonempty (AbsConvexOpenSets 𝕜 E) := by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, is_open_univ, balancedUniv, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [IsROrC 𝕜]

variable [AddCommGroup E] [TopologicalSpace E]

variable [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]

variable [HasContinuousSmul ℝ E]

variable (𝕜 E)

/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coeBalanced s.coe_convex (absorbentNhdsZero s.coe_nhds)
#align gauge_seminorm_family gaugeSeminormFamily

variable {𝕜 E}

theorem gauge_seminorm_family_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) := by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gauge_seminorm_to_fun]
  exact gauge_lt_one_eq_self_of_open s.coe_convex s.coe_zero_mem s.coe_is_open
#align gauge_seminorm_family_ball gauge_seminorm_family_ball

variable [TopologicalAddGroup E] [HasContinuousSmul 𝕜 E]

variable [SMulCommClass ℝ 𝕜 E] [LocallyConvexSpace ℝ E]

/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
theorem withGaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) := by
  refine' SeminormFamily.withSeminormsOfHasBasis _ _
  refine'
    Filter.HasBasis.to_has_basis (nhds_basis_abs_convex_open 𝕜 E) (fun s hs => _) fun s hs => _
  · refine' ⟨s, ⟨_, rfl.subset⟩⟩
    rw [SeminormFamily.basis_sets_iff]
    refine' ⟨{⟨s, hs⟩}, 1, one_pos, _⟩
    simp only [Finset.sup_singleton]
    rw [gauge_seminorm_family_ball]
    simp only [Subtype.coe_mk]
  refine' ⟨s, ⟨_, rfl.subset⟩⟩
  rw [SeminormFamily.basis_sets_iff] at hs
  rcases hs with ⟨t, r, hr, hs⟩
  rw [Seminorm.ball_finset_sup_eq_Inter _ _ _ hr] at hs
  rw [hs]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine'
    ⟨mem_Inter₂.mpr fun _ _ => by simp [Seminorm.mem_ball_zero, hr],
      is_open_bInter (to_finite _) fun _ _ => _,
      balancedInter₂ fun _ _ => Seminorm.balancedBallZero _ _,
      convex_Inter₂ fun _ _ => Seminorm.convex_ball _ _ _⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) ≠ 0 := by simp [ne_of_gt hr]
  rw [hr']
  rw [← Seminorm.smul_ball_zero (norm_pos_iff.mpr hr'')]
  refine' IsOpen.smul₀ _ hr''
  rw [gauge_seminorm_family_ball]
  exact AbsConvexOpenSets.coe_is_open _
#align with_gauge_seminorm_family withGaugeSeminormFamily

