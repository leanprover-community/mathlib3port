/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module topology.local_at_target
! leanprover-community/mathlib commit d3e8e0a0237c10c2627bf52c246b15ff8e7df4c0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Sets.Opens

/-!
# Properties of maps that are local at the target.

We show that the following properties of continuous maps are local at the target :
- `inducing`
- `embedding`
- `open_embedding`
- `closed_embedding`

-/


open TopologicalSpace Set Filter

open TopologicalSpace Filter

variable {α β : Type _} [TopologicalSpace α] [TopologicalSpace β] {f : α → β}

variable {s : Set β} {ι : Type _} {U : ι → Opens β} (hU : supᵢ U = ⊤)

theorem Set.restrict_preimage_inducing (s : Set β) (h : Inducing f) :
    Inducing (s.restrictPreimage f) :=
  by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @Filter.comap_comap _ _ _ _ coe f] at h⊢
  intro a
  rw [← h, ← inducing_coe.nhds_eq_comap]
#align set.restrict_preimage_inducing Set.restrict_preimage_inducing

alias Set.restrict_preimage_inducing ← Inducing.restrict_preimage

theorem Set.restrict_preimage_embedding (s : Set β) (h : Embedding f) :
    Embedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩
#align set.restrict_preimage_embedding Set.restrict_preimage_embedding

alias Set.restrict_preimage_embedding ← Embedding.restrict_preimage

theorem Set.restrict_preimage_open_embedding (s : Set β) (h : OpenEmbedding f) :
    OpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrict_preimage f).symm ▸ continuous_subtype_coe.is_open_preimage _ h.2⟩
#align set.restrict_preimage_open_embedding Set.restrict_preimage_open_embedding

alias Set.restrict_preimage_open_embedding ← OpenEmbedding.restrict_preimage

theorem Set.restrict_preimage_closed_embedding (s : Set β) (h : ClosedEmbedding f) :
    ClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s,
    (s.range_restrict_preimage f).symm ▸ inducing_coe.is_closed_preimage _ h.2⟩
#align set.restrict_preimage_closed_embedding Set.restrict_preimage_closed_embedding

alias Set.restrict_preimage_closed_embedding ← ClosedEmbedding.restrict_preimage

theorem Set.restrict_preimage_is_closed_map (s : Set β) (H : IsClosedMap f) :
    IsClosedMap (s.restrictPreimage f) :=
  by
  rintro t ⟨u, hu, e⟩
  refine' ⟨⟨_, (H _ (IsOpen.is_closed_compl hu)).1, _⟩⟩
  rw [← (congr_arg HasCompl.compl e).trans (compl_compl t)]
  simp only [Set.preimage_compl, compl_inj_iff]
  ext ⟨x, hx⟩
  suffices (∃ y, y ∉ u ∧ f y = x) ↔ ∃ y, f y ∈ s ∧ y ∉ u ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c.symm ▸ hx, b, c⟩, fun ⟨a, _, b, c⟩ => ⟨a, b, c⟩⟩
#align set.restrict_preimage_is_closed_map Set.restrict_preimage_is_closed_map

include hU

theorem is_open_iff_inter_of_supr_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) :=
  by
  constructor
  · exact fun H i => H.inter (U i).2
  · intro H
    have : (⋃ i, (U i : Set β)) = Set.univ :=
      by
      convert congr_arg coe hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_unionᵢ]
    exact is_open_Union H
#align is_open_iff_inter_of_supr_eq_top is_open_iff_inter_of_supr_eq_top

theorem is_open_iff_coe_preimage_of_supr_eq_top (s : Set β) :
    IsOpen s ↔ ∀ i, IsOpen (coe ⁻¹' s : Set (U i)) :=
  by
  simp_rw [(U _).2.open_embedding_subtype_coe.open_iff_image_open,
    Set.image_preimage_eq_inter_range, Subtype.range_coe]
  apply is_open_iff_inter_of_supr_eq_top
  assumption
#align is_open_iff_coe_preimage_of_supr_eq_top is_open_iff_coe_preimage_of_supr_eq_top

theorem is_closed_iff_coe_preimage_of_supr_eq_top (s : Set β) :
    IsClosed s ↔ ∀ i, IsClosed (coe ⁻¹' s : Set (U i)) := by
  simpa using is_open_iff_coe_preimage_of_supr_eq_top hU (sᶜ)
#align is_closed_iff_coe_preimage_of_supr_eq_top is_closed_iff_coe_preimage_of_supr_eq_top

theorem is_closed_map_iff_is_closed_map_of_supr_eq_top :
    IsClosedMap f ↔ ∀ i, IsClosedMap ((U i).1.restrictPreimage f) :=
  by
  refine' ⟨fun h i => Set.restrict_preimage_is_closed_map _ h, _⟩
  rintro H s hs
  rw [is_closed_iff_coe_preimage_of_supr_eq_top hU]
  intro i
  convert H i _ ⟨⟨_, hs.1, eq_compl_comm.mpr rfl⟩⟩
  ext ⟨x, hx⟩
  suffices (∃ y, y ∈ s ∧ f y = x) ↔ ∃ y, f y ∈ U i ∧ y ∈ s ∧ f y = x by
    simpa [Set.restrictPreimage, ← Subtype.coe_inj]
  exact ⟨fun ⟨a, b, c⟩ => ⟨a, c.symm ▸ hx, b, c⟩, fun ⟨a, _, b, c⟩ => ⟨a, b, c⟩⟩
#align is_closed_map_iff_is_closed_map_of_supr_eq_top is_closed_map_iff_is_closed_map_of_supr_eq_top

theorem inducing_iff_inducing_of_supr_eq_top (h : Continuous f) :
    Inducing f ↔ ∀ i, Inducing ((U i).1.restrictPreimage f) :=
  by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict,
    restrict_eq, ← @Filter.comap_comap _ _ _ _ coe f]
  constructor
  · intro H i x
    rw [← H, ← inducing_coe.nhds_eq_comap]
  · intro H x
    obtain ⟨i, hi⟩ :=
      opens.mem_supr.mp
        (show f x ∈ supᵢ U by
          rw [hU]
          triv)
    erw [← OpenEmbedding.map_nhds_eq (h.1 _ (U i).2).open_embedding_subtype_coe ⟨x, hi⟩]
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_apply, Subtype.coe_mk,
      inf_eq_left, Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)
#align inducing_iff_inducing_of_supr_eq_top inducing_iff_inducing_of_supr_eq_top

theorem embedding_iff_embedding_of_supr_eq_top (h : Continuous f) :
    Embedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply inducing_iff_inducing_of_supr_eq_top <;> assumption
  · apply Set.injective_iff_injective_of_unionᵢ_eq_univ
    convert congr_arg coe hU
    simp
#align embedding_iff_embedding_of_supr_eq_top embedding_iff_embedding_of_supr_eq_top

theorem open_embedding_iff_open_embedding_of_supr_eq_top (h : Continuous f) :
    OpenEmbedding f ↔ ∀ i, OpenEmbedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [open_embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_supr_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply is_open_iff_coe_preimage_of_supr_eq_top hU
#align
  open_embedding_iff_open_embedding_of_supr_eq_top open_embedding_iff_open_embedding_of_supr_eq_top

theorem closed_embedding_iff_closed_embedding_of_supr_eq_top (h : Continuous f) :
    ClosedEmbedding f ↔ ∀ i, ClosedEmbedding ((U i).1.restrictPreimage f) :=
  by
  simp_rw [closed_embedding_iff]
  rw [forall_and]
  apply and_congr
  · apply embedding_iff_embedding_of_supr_eq_top <;> assumption
  · simp_rw [Set.range_restrictPreimage]
    apply is_closed_iff_coe_preimage_of_supr_eq_top hU
#align
  closed_embedding_iff_closed_embedding_of_supr_eq_top closed_embedding_iff_closed_embedding_of_supr_eq_top

