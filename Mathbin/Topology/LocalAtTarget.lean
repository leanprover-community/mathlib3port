/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
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

variable {s : Set β} {ι : Type _} {U : ι → Opens β} (hU : supr U = ⊤)

theorem Set.restrict_preimage_inducing (s : Set β) (h : Inducing f) : Inducing (s.restrictPreimage f) := by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict, restrict_eq, ←
    @Filter.comap_comap _ _ _ _ coe f] at h⊢
  intro a
  rw [← h, ← inducing_coe.nhds_eq_comap]

alias Set.restrict_preimage_inducing ← Inducing.restrict_preimage

theorem Set.restrict_preimage_embedding (s : Set β) (h : Embedding f) : Embedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, h.2.restrictPreimage s⟩

alias Set.restrict_preimage_embedding ← Embedding.restrict_preimage

theorem Set.restrict_preimage_open_embedding (s : Set β) (h : OpenEmbedding f) : OpenEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, (s.range_restrict_preimage f).symm ▸ continuous_subtype_coe.is_open_preimage _ h.2⟩

alias Set.restrict_preimage_open_embedding ← OpenEmbedding.restrict_preimage

theorem Set.restrict_preimage_closed_embedding (s : Set β) (h : ClosedEmbedding f) :
    ClosedEmbedding (s.restrictPreimage f) :=
  ⟨h.1.restrictPreimage s, (s.range_restrict_preimage f).symm ▸ inducing_coe.is_closed_preimage _ h.2⟩

alias Set.restrict_preimage_closed_embedding ← ClosedEmbedding.restrict_preimage

include hU

theorem open_iff_inter_of_supr_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (s ∩ U i) := by
  constructor
  · exact fun H i => H.inter (U i).2
    
  · intro H
    have : (⋃ i, (U i : Set β)) = Set.Univ := by
      convert congr_arg coe hU
      simp
    rw [← s.inter_univ, ← this, Set.inter_Union]
    exact is_open_Union H
    

theorem open_iff_coe_preimage_of_supr_eq_top (s : Set β) : IsOpen s ↔ ∀ i, IsOpen (coe ⁻¹' s : Set (U i)) := by
  simp_rw [(U _).2.open_embedding_subtype_coe.open_iff_image_open, Set.image_preimage_eq_inter_range, Subtype.range_coe]
  apply open_iff_inter_of_supr_eq_top
  assumption

theorem closed_iff_coe_preimage_of_supr_eq_top (s : Set β) : IsClosed s ↔ ∀ i, IsClosed (coe ⁻¹' s : Set (U i)) := by
  simpa using open_iff_coe_preimage_of_supr_eq_top hU (sᶜ)

theorem inducing_iff_inducing_of_supr_eq_top (h : Continuous f) :
    Inducing f ↔ ∀ i, Inducing ((U i).1.restrictPreimage f) := by
  simp_rw [inducing_coe.inducing_iff, inducing_iff_nhds, restrict_preimage, maps_to.coe_restrict, restrict_eq, ←
    @Filter.comap_comap _ _ _ _ coe f]
  constructor
  · intro H i x
    rw [← H, ← inducing_coe.nhds_eq_comap]
    
  · intro H x
    obtain ⟨i, hi⟩ :=
      opens.mem_supr.mp
        (show f x ∈ supr U by
          rw [hU]
          triv)
    erw [← OpenEmbedding.map_nhds_eq (h.1 _ (U i).2).open_embedding_subtype_coe ⟨x, hi⟩]
    rw [(H i) ⟨x, hi⟩, Filter.subtype_coe_map_comap, Function.comp_applyₓ, Subtype.coe_mk, inf_eq_left,
      Filter.le_principal_iff]
    exact Filter.preimage_mem_comap ((U i).2.mem_nhds hi)
    

theorem embedding_iff_embedding_of_supr_eq_top (h : Continuous f) :
    Embedding f ↔ ∀ i, Embedding ((U i).1.restrictPreimage f) := by
  simp_rw [embedding_iff]
  rw [forall_and_distrib]
  apply and_congr
  · apply inducing_iff_inducing_of_supr_eq_top <;> assumption
    
  · apply Set.injective_iff_injective_of_Union_eq_univ
    convert congr_arg coe hU
    simp
    

theorem open_embedding_iff_open_embedding_of_supr_eq_top (h : Continuous f) :
    OpenEmbedding f ↔ ∀ i, OpenEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [open_embedding_iff]
  rw [forall_and_distrib]
  apply and_congr
  · apply embedding_iff_embedding_of_supr_eq_top <;> assumption
    
  · simp_rw [Set.range_restrict_preimage]
    apply open_iff_coe_preimage_of_supr_eq_top hU
    

theorem closed_embedding_iff_closed_embedding_of_supr_eq_top (h : Continuous f) :
    ClosedEmbedding f ↔ ∀ i, ClosedEmbedding ((U i).1.restrictPreimage f) := by
  simp_rw [closed_embedding_iff]
  rw [forall_and_distrib]
  apply and_congr
  · apply embedding_iff_embedding_of_supr_eq_top <;> assumption
    
  · simp_rw [Set.range_restrict_preimage]
    apply closed_iff_coe_preimage_of_supr_eq_top hU
    

