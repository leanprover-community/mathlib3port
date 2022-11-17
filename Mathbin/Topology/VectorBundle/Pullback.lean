/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Floris van Doorn
-/
import Mathbin.Topology.VectorBundle.Basic

/-!
# Pullbacks of fiber and vector bundles

We construct the pullback bundle for a map `f : B' → B` whose fiber map is given simply by
`f *ᵖ E = E ∘ f` (the type synonym is there for typeclass instance problems).
-/


noncomputable section

open Bundle Set TopologicalSpace

open Classical Bundle

variable (R 𝕜 : Type _) {B : Type _} (F : Type _) (E E' : B → Type _)

variable {B' : Type _} (f : B' → B)

instance [∀ x : B, TopologicalSpace (E' x)] : ∀ x : B', TopologicalSpace ((f *ᵖ E') x) := by
  delta_instance bundle.pullback

instance [∀ x : B, AddCommMonoid (E' x)] : ∀ x : B', AddCommMonoid ((f *ᵖ E') x) := by delta_instance bundle.pullback

instance [Semiring R] [∀ x : B, AddCommMonoid (E' x)] [∀ x, Module R (E' x)] : ∀ x : B', Module R ((f *ᵖ E') x) := by
  delta_instance bundle.pullback

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace E)]

/-- Definition of `pullback.total_space.topological_space`, which we make irreducible. -/
irreducible_def pullbackTopology : TopologicalSpace (TotalSpace (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓ induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace E)›
#align pullback_topology pullbackTopology

/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace (f *ᵖ E)) :=
  pullbackTopology E f
#align pullback.total_space.topological_space Pullback.TotalSpace.topologicalSpace

theorem Pullback.continuous_proj (f : B' → B) : Continuous (@TotalSpace.proj _ (f *ᵖ E)) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  exact inf_le_left
#align pullback.continuous_proj Pullback.continuous_proj

theorem Pullback.continuous_lift (f : B' → B) : Continuous (@Pullback.lift B E B' f) := by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  exact inf_le_right
#align pullback.continuous_lift Pullback.continuous_lift

theorem inducing_pullback_total_space_embedding (f : B' → B) : Inducing (@pullbackTotalSpaceEmbedding B E B' f) := by
  constructor
  simp_rw [Prod.topologicalSpace, induced_inf, induced_compose, Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  rfl
#align inducing_pullback_total_space_embedding inducing_pullback_total_space_embedding

section FiberBundle

variable (F) [TopologicalSpace F] [TopologicalSpace B]

theorem Pullback.continuous_total_space_mk [∀ x, TopologicalSpace (E x)] [FiberBundle F E] {f : B' → B} {x : B'} :
    Continuous (@totalSpaceMk _ (f *ᵖ E) x) := by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose, induced_inf,
    Function.comp, total_space_mk, total_space.proj, induced_const, top_inf_eq, pullbackTopology]
  exact le_of_eq (FiberBundle.total_space_mk_inducing F E (f x)).induced
#align pullback.continuous_total_space_mk Pullback.continuous_total_space_mk

variable {E F} [∀ b, Zero (E b)] {K : Type _} [ContinuousMapClass K B' B]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
def Trivialization.pullback (e : Trivialization F (π E)) (f : K) : Trivialization F (π ((f : B' → B) *ᵖ E)) where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := @totalSpaceMk _ (f *ᵖ E) y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h := by
    simp_rw [e.source_eq, mem_preimage, pullback.proj_lift] at h
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod, mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, pullback.proj_lift, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, pullback.proj_lift] at h
    simp_rw [pullback.lift, e.symm_apply_apply_mk h, total_space.eta]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true_iff] at h
    simp_rw [total_space.proj_mk, pullback.lift_mk, e.apply_mk_symm h, Prod.mk.eta]
  open_source := by
    simp_rw [e.source_eq, ← preimage_comp]
    exact ((map_continuous f).comp $ Pullback.continuous_proj E f).is_open_preimage _ e.open_base_set
  open_target := ((map_continuous f).is_open_preimage _ e.open_base_set).Prod is_open_univ
  open_base_set := (map_continuous f).is_open_preimage _ e.open_base_set
  continuous_to_fun :=
    (Pullback.continuous_proj E f).ContinuousOn.Prod
      (continuous_snd.comp_continuous_on $ e.ContinuousOn.comp (Pullback.continuous_lift E f).ContinuousOn Subset.rfl)
  continuous_inv_fun := by
    dsimp only
    simp_rw [(inducing_pullback_total_space_embedding E f).continuous_on_iff, Function.comp,
      pullback_total_space_embedding, total_space.proj_mk]
    dsimp only [total_space.proj_mk]
    refine'
      continuous_on_fst.prod
        (e.continuous_on_symm.comp ((map_continuous f).prod_map continuous_id).ContinuousOn subset.rfl)
  source_eq := by
    dsimp only
    rw [e.source_eq]
    rfl
  target_eq := rfl
  proj_to_fun y h := rfl
#align trivialization.pullback Trivialization.pullback

instance FiberBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E] (f : K) :
    FiberBundle F ((f : B' → B) *ᵖ E) where
  total_space_mk_inducing x :=
    inducing_of_inducing_compose (Pullback.continuous_total_space_mk F E) (Pullback.continuous_lift E f)
      (total_space_mk_inducing F E (f x))
  trivializationAtlas := { ef | ∃ (e : Trivialization F (π E)) (_ : MemTrivializationAtlas e), ef = e.pullback f }
  trivializationAt x := (trivializationAt F E (f x)).pullback f
  mem_base_set_trivialization_at x := mem_base_set_trivialization_at F E (f x)
  trivialization_mem_atlas x := ⟨trivializationAt F E (f x), by infer_instance, rfl⟩
#align fiber_bundle.pullback FiberBundle.pullback

end FiberBundle

section VectorBundle

variable (F) [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace B]
  [∀ x, AddCommMonoid (E x)] [∀ x, Module 𝕜 (E x)]

variable {E F} {K : Type _} [ContinuousMapClass K B' B]

instance Trivialization.pullback_linear (e : Trivialization F (π E)) [e.is_linear 𝕜] (f : K) :
    (@Trivialization.pullback _ _ _ B' _ _ _ _ _ _ _ e f).is_linear 𝕜 where linear x h := e.linear 𝕜 h
#align trivialization.pullback_linear Trivialization.pullback_linear

instance VectorBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E] (f : K) :
    VectorBundle 𝕜 F ((f : B' → B) *ᵖ E) where
  trivialization_linear' := by
    rintro _ ⟨e, he, rfl⟩
    skip
    infer_instance
  continuous_on_coord_change' := by
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩
    skip
    refine' ((continuous_on_coord_change 𝕜 e e').comp (map_continuous f).ContinuousOn fun b hb => hb).congr _
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set)
    ext v
    show ((e.pullback f).coordChangeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v
    rw [e.coord_changeL_apply e' hb, (e.pullback f).coord_changeL_apply' _]
    exacts[rfl, hb]
#align vector_bundle.pullback VectorBundle.pullback

end VectorBundle

