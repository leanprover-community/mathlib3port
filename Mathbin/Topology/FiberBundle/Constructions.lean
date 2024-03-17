/-
Copyright © 2022 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sébastien Gouëzel, Heather Macbeth, Floris van Doorn
-/
import Topology.FiberBundle.Basic

#align_import topology.fiber_bundle.constructions from "leanprover-community/mathlib"@"e473c3198bb41f68560cab68a0529c854b618833"

/-!
# Standard constructions on fiber bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains several standard constructions on fiber bundles:

* `bundle.trivial.fiber_bundle 𝕜 B F`: the trivial fiber bundle with model fiber `F` over the base
  `B`

* `fiber_bundle.prod`: for fiber bundles `E₁` and `E₂` over a common base, a fiber bundle structure
  on their fiberwise product `E₁ ×ᵇ E₂` (the notation stands for `λ x, E₁ x × E₂ x`).

* `fiber_bundle.pullback`: for a fiber bundle `E` over `B`, a fiber bundle structure on its
  pullback `f *ᵖ E` by a map `f : B' → B` (the notation is a type synonym for `E ∘ f`).

## Tags

fiber bundle, fibre bundle, fiberwise product, pullback

-/


open TopologicalSpace Filter Set Bundle

open scoped Topology Classical Bundle

/-! ### The trivial bundle -/


namespace Bundle

namespace trivial

variable (B : Type _) (F : Type _)

instance [t₁ : TopologicalSpace B] [t₂ : TopologicalSpace F] :
    TopologicalSpace (TotalSpace F (Trivial B F)) :=
  induced TotalSpace.proj t₁ ⊓ induced (TotalSpace.trivialSnd B F) t₂

variable [TopologicalSpace B] [TopologicalSpace F]

#print Bundle.Trivial.trivialization /-
/-- Local trivialization for trivial bundle. -/
def trivialization : Trivialization F (π F fun _ : B => F)
    where
  toFun x := (x.proj, x.snd)
  invFun y := ⟨y.fst, y.snd⟩
  source := univ
  target := univ
  map_source' x h := mem_univ _
  map_target' y h := mem_univ _
  left_inv' x h := TotalSpace.ext _ _ rfl HEq.rfl
  right_inv' x h := Prod.ext rfl rfl
  open_source := isOpen_univ
  open_target := isOpen_univ
  continuous_toFun :=
    by
    rw [← continuous_iff_continuousOn_univ, continuous_iff_le_induced]
    simp only [Prod.topologicalSpace, induced_inf, induced_compose]; exact le_rfl
  continuous_invFun :=
    by
    rw [← continuous_iff_continuousOn_univ, continuous_iff_le_induced]
    simp only [bundle.total_space.topological_space, induced_inf, induced_compose]
    exact le_rfl
  baseSet := univ
  open_baseSet := isOpen_univ
  source_eq := rfl
  target_eq := by simp only [univ_prod_univ]
  proj_toFun y hy := rfl
#align bundle.trivial.trivialization Bundle.Trivial.trivialization
-/

#print Bundle.Trivial.trivialization_source /-
@[simp]
theorem trivialization_source : (trivialization B F).source = univ :=
  rfl
#align bundle.trivial.trivialization_source Bundle.Trivial.trivialization_source
-/

#print Bundle.Trivial.trivialization_target /-
@[simp]
theorem trivialization_target : (trivialization B F).target = univ :=
  rfl
#align bundle.trivial.trivialization_target Bundle.Trivial.trivialization_target
-/

#print Bundle.Trivial.fiberBundle /-
/-- Fiber bundle instance on the trivial bundle. -/
instance fiberBundle : FiberBundle F (Bundle.Trivial B F)
    where
  trivializationAtlas := {Bundle.Trivial.trivialization B F}
  trivializationAt x := Bundle.Trivial.trivialization B F
  mem_baseSet_trivializationAt := mem_univ
  trivialization_mem_atlas x := mem_singleton _
  totalSpace_mk_inducing b :=
    ⟨by
      have : (fun x : trivial B F b => x) = @id F := by ext x; rfl
      simp only [total_space.topological_space, induced_inf, induced_compose, Function.comp,
        induced_const, top_inf_eq, total_space.trivial_snd, id.def, this, induced_id]⟩
#align bundle.trivial.fiber_bundle Bundle.Trivial.fiberBundle
-/

#print Bundle.Trivial.eq_trivialization /-
theorem eq_trivialization (e : Trivialization F (π F (Bundle.Trivial B F)))
    [i : MemTrivializationAtlas e] : e = trivialization B F :=
  i.out
#align bundle.trivial.eq_trivialization Bundle.Trivial.eq_trivialization
-/

end trivial

end Bundle

/-! ### Fibrewise product of two bundles -/


section Prod

variable {B : Type _}

section Defs

variable (F₁ : Type _) (E₁ : B → Type _) (F₂ : Type _) (E₂ : B → Type _)

variable [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]

#print FiberBundle.Prod.topologicalSpace /-
/-- Equip the total space of the fiberwise product of two fiber bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `total_space E₁ × total_space E₂`. -/
instance FiberBundle.Prod.topologicalSpace : TopologicalSpace (TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)) :=
  TopologicalSpace.induced
    (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace F₁ E₁), (⟨p.1, p.2.2⟩ : TotalSpace F₂ E₂)))
    (by infer_instance : TopologicalSpace (TotalSpace F₁ E₁ × TotalSpace F₂ E₂))
#align fiber_bundle.prod.topological_space FiberBundle.Prod.topologicalSpace
-/

#print FiberBundle.Prod.inducing_diag /-
/-- The diagonal map from the total space of the fiberwise product of two fiber bundles
`E₁`, `E₂` into `total_space E₁ × total_space E₂` is `inducing`. -/
theorem FiberBundle.Prod.inducing_diag :
    Inducing
      (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) :
        TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → TotalSpace F₁ E₁ × TotalSpace F₂ E₂) :=
  ⟨rfl⟩
#align fiber_bundle.prod.inducing_diag FiberBundle.Prod.inducing_diag
-/

end Defs

open FiberBundle

variable [TopologicalSpace B] (F₁ : Type _) [TopologicalSpace F₁] (E₁ : B → Type _)
  [TopologicalSpace (TotalSpace F₁ E₁)] (F₂ : Type _) [TopologicalSpace F₂] (E₂ : B → Type _)
  [TopologicalSpace (TotalSpace F₂ E₂)]

namespace Trivialization

variable {F₁ E₁ F₂ E₂} (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))

#print Trivialization.Prod.toFun' /-
/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
def Prod.toFun' : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) → B × F₁ × F₂ := fun p =>
  ⟨p.1, (e₁ ⟨p.1, p.2.1⟩).2, (e₂ ⟨p.1, p.2.2⟩).2⟩
#align trivialization.prod.to_fun' Trivialization.Prod.toFun'
-/

variable {e₁ e₂}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Trivialization.Prod.continuous_to_fun /-
theorem Prod.continuous_to_fun :
    ContinuousOn (Prod.toFun' e₁ e₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) :=
  by
  let f₁ : total_space (F₁ × F₂) (E₁ ×ᵇ E₂) → total_space F₁ E₁ × total_space F₂ E₂ := fun p =>
    ((⟨p.1, p.2.1⟩ : total_space F₁ E₁), (⟨p.1, p.2.2⟩ : total_space F₂ E₂))
  let f₂ : total_space F₁ E₁ × total_space F₂ E₂ → (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ → B × F₁ × F₂ := fun p => ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (prod.inducing_diag F₁ E₁ F₂ E₂).Continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on
  have hf₃ : Continuous f₃ :=
    (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd)
  refine' ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _
  · rw [e₁.source_eq, e₂.source_eq]
    exact maps_to_preimage _ _
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩
  simp only [prod.to_fun', Prod.mk.inj_iff, eq_self_iff_true, and_true_iff]
  rw [e₁.coe_fst]
  rw [e₁.source_eq, mem_preimage]
  exact hb₁
#align trivialization.prod.continuous_to_fun Trivialization.Prod.continuous_to_fun
-/

variable (e₁ e₂) [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)]

#print Trivialization.Prod.invFun' /-
/-- Given trivializations `e₁`, `e₂` for fiber bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `trivialization.prod`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`. -/
noncomputable def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂) :=
  ⟨p.1, e₁.symm p.1 p.2.1, e₂.symm p.1 p.2.2⟩
#align trivialization.prod.inv_fun' Trivialization.Prod.invFun'
-/

variable {e₁ e₂}

#print Trivialization.Prod.left_inv /-
theorem Prod.left_inv {x : TotalSpace (F₁ × F₂) (E₁ ×ᵇ E₂)}
    (h : x ∈ π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x :=
  by
  obtain ⟨x, v₁, v₂⟩ := x
  obtain ⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩ := h
  simp only [prod.to_fun', prod.inv_fun', symm_apply_apply_mk, h₁, h₂, eq_self_iff_true, heq_iff_eq,
    and_self_iff]
#align trivialization.prod.left_inv Trivialization.Prod.left_inv
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Trivialization.Prod.right_inv /-
theorem Prod.right_inv {x : B × F₁ × F₂}
    (h : x ∈ (e₁.baseSet ∩ e₂.baseSet) ×ˢ (univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x :=
  by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨⟨h₁ : x ∈ e₁.base_set, h₂ : x ∈ e₂.base_set⟩, -⟩ := h
  simp only [prod.to_fun', prod.inv_fun', apply_mk_symm, h₁, h₂]
#align trivialization.prod.right_inv Trivialization.Prod.right_inv
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Trivialization.Prod.continuous_inv_fun /-
theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.baseSet ∩ e₂.baseSet) ×ˢ univ) :=
  by
  rw [(prod.inducing_diag F₁ E₁ F₂ E₂).continuousOn_iff]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd)
  refine' (e₁.continuous_on_symm.prod_map e₂.continuous_on_symm).comp H₁.continuous_on _
  exact fun x h => ⟨⟨h.1.1, mem_univ _⟩, ⟨h.1.2, mem_univ _⟩⟩
#align trivialization.prod.continuous_inv_fun Trivialization.Prod.continuous_inv_fun
-/

variable (e₁ e₂)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Trivialization.prod /-
/-- Given trivializations `e₁`, `e₂` for bundle types `E₁`, `E₂` over a base `B`, the induced
trivialization for the fiberwise product of `E₁` and `E₂`, whose base set is
`e₁.base_set ∩ e₂.base_set`. -/
noncomputable def prod : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂))
    where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  source := π (F₁ × F₂) (E₁ ×ᵇ E₂) ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' x h := ⟨h, Set.mem_univ _⟩
  map_target' x h := h.1
  left_inv' x := Prod.left_inv
  right_inv' x := Prod.right_inv
  open_source :=
    by
    convert
      (e₁.open_source.prod e₂.open_source).Preimage
        (FiberBundle.Prod.inducing_diag F₁ E₁ F₂ E₂).Continuous
    ext x
    simp only [Trivialization.source_eq, mfld_simps]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).Prod isOpen_univ
  continuous_toFun := Prod.continuous_to_fun
  continuous_invFun := Prod.continuous_inv_fun
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun x h := rfl
#align trivialization.prod Trivialization.prod
-/

#print Trivialization.baseSet_prod /-
@[simp]
theorem baseSet_prod : (prod e₁ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl
#align trivialization.base_set_prod Trivialization.baseSet_prod
-/

#print Trivialization.prod_symm_apply /-
theorem prod_symm_apply (x : B) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toPartialEquiv.symm (x, w₁, w₂) = ⟨x, e₁.symm x w₁, e₂.symm x w₂⟩ :=
  rfl
#align trivialization.prod_symm_apply Trivialization.prod_symm_apply
-/

end Trivialization

open Trivialization

variable [∀ x, Zero (E₁ x)] [∀ x, Zero (E₂ x)] [∀ x : B, TopologicalSpace (E₁ x)]
  [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₁ E₁] [FiberBundle F₂ E₂]

#print FiberBundle.prod /-
/-- The product of two fiber bundles is a fiber bundle. -/
noncomputable instance FiberBundle.prod : FiberBundle (F₁ × F₂) (E₁ ×ᵇ E₂)
    where
  totalSpace_mk_inducing b :=
    by
    rw [(prod.inducing_diag F₁ E₁ F₂ E₂).inducing_iff]
    exact (total_space_mk_inducing F₁ E₁ b).prod_mk (total_space_mk_inducing F₂ E₂ b)
  trivializationAtlas :=
    {e |
      ∃ (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂)) (_ :
        MemTrivializationAtlas e₁) (_ : MemTrivializationAtlas e₂), e = Trivialization.prod e₁ e₂}
  trivializationAt b := (trivializationAt F₁ E₁ b).Prod (trivializationAt F₂ E₂ b)
  mem_baseSet_trivializationAt b :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ b, mem_baseSet_trivializationAt F₂ E₂ b⟩
  trivialization_mem_atlas b :=
    ⟨trivializationAt F₁ E₁ b, trivializationAt F₂ E₂ b, by infer_instance, by infer_instance, rfl⟩
#align fiber_bundle.prod FiberBundle.prod
-/

instance {e₁ : Trivialization F₁ (π F₁ E₁)} {e₂ : Trivialization F₂ (π F₂ E₂)}
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂] :
    MemTrivializationAtlas (e₁.Prod e₂ : Trivialization (F₁ × F₂) (π (F₁ × F₂) (E₁ ×ᵇ E₂)))
    where out := ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩

end Prod

/-! ### Pullbacks of fiber bundles -/


section

variable {B : Type _} (F : Type _) (E : B → Type _) {B' : Type _} (f : B' → B)

instance [∀ x : B, TopologicalSpace (E x)] : ∀ x : B', TopologicalSpace ((f *ᵖ E) x) := by
  delta_instance bundle.pullback

variable [TopologicalSpace B'] [TopologicalSpace (TotalSpace F E)]

#print pullbackTopology /-
/-- Definition of `pullback.total_space.topological_space`, which we make irreducible. -/
irreducible_def pullbackTopology : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  induced TotalSpace.proj ‹TopologicalSpace B'› ⊓
    induced (Pullback.lift f) ‹TopologicalSpace (TotalSpace F E)›
#align pullback_topology pullbackTopology
-/

#print Pullback.TotalSpace.topologicalSpace /-
/-- The topology on the total space of a pullback bundle is the coarsest topology for which both
the projections to the base and the map to the original bundle are continuous. -/
instance Pullback.TotalSpace.topologicalSpace : TopologicalSpace (TotalSpace F (f *ᵖ E)) :=
  pullbackTopology F E f
#align pullback.total_space.topological_space Pullback.TotalSpace.topologicalSpace
-/

#print Pullback.continuous_proj /-
theorem Pullback.continuous_proj (f : B' → B) : Continuous (π F (f *ᵖ E)) :=
  by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  exact inf_le_left
#align pullback.continuous_proj Pullback.continuous_proj
-/

#print Pullback.continuous_lift /-
theorem Pullback.continuous_lift (f : B' → B) : Continuous (@Pullback.lift B F E B' f) :=
  by
  rw [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  exact inf_le_right
#align pullback.continuous_lift Pullback.continuous_lift
-/

#print inducing_pullbackTotalSpaceEmbedding /-
theorem inducing_pullbackTotalSpaceEmbedding (f : B' → B) :
    Inducing (@pullbackTotalSpaceEmbedding B F E B' f) :=
  by
  constructor
  simp_rw [Prod.topologicalSpace, induced_inf, induced_compose,
    Pullback.TotalSpace.topologicalSpace, pullbackTopology]
  rfl
#align inducing_pullback_total_space_embedding inducing_pullbackTotalSpaceEmbedding
-/

section FiberBundle

variable (F) [TopologicalSpace F] [TopologicalSpace B]

#print Pullback.continuous_totalSpaceMk /-
theorem Pullback.continuous_totalSpaceMk [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    {f : B' → B} {x : B'} : Continuous (@TotalSpace.mk _ F (f *ᵖ E) x) :=
  by
  simp only [continuous_iff_le_induced, Pullback.TotalSpace.topologicalSpace, induced_compose,
    induced_inf, Function.comp, induced_const, top_inf_eq, pullbackTopology]
  exact le_of_eq (FiberBundle.totalSpace_mk_inducing F E (f x)).induced
#align pullback.continuous_total_space_mk Pullback.continuous_totalSpaceMk
-/

variable {E F} [∀ b, Zero (E b)] {K : Type _} [ContinuousMapClass K B' B]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print Trivialization.pullback /-
/-- A fiber bundle trivialization can be pulled back to a trivialization on the pullback bundle. -/
noncomputable def Trivialization.pullback (e : Trivialization F (π F E)) (f : K) :
    Trivialization F (π F ((f : B' → B) *ᵖ E))
    where
  toFun z := (z.proj, (e (Pullback.lift f z)).2)
  invFun y := @TotalSpace.mk _ _ (f *ᵖ E) y.1 (e.symm (f y.1) y.2)
  source := Pullback.lift f ⁻¹' e.source
  baseSet := f ⁻¹' e.baseSet
  target := (f ⁻¹' e.baseSet) ×ˢ univ
  map_source' x h :=
    by
    simp_rw [e.source_eq, mem_preimage, pullback.lift_proj] at h
    simp_rw [prod_mk_mem_set_prod_eq, mem_univ, and_true_iff, mem_preimage, h]
  map_target' y h := by
    rw [mem_prod, mem_preimage] at h
    simp_rw [e.source_eq, mem_preimage, pullback.lift_proj, h.1]
  left_inv' x h := by
    simp_rw [mem_preimage, e.mem_source, pullback.lift_proj] at h
    simp_rw [pullback.lift, e.symm_apply_apply_mk h, total_space.eta]
  right_inv' x h := by
    simp_rw [mem_prod, mem_preimage, mem_univ, and_true_iff] at h
    simp_rw [pullback.lift_mk, e.apply_mk_symm h, Prod.mk.eta]
  open_source := by simp_rw [e.source_eq, ← preimage_comp];
    exact
      ((map_continuous f).comp <| Pullback.continuous_proj F E f).isOpen_preimage _ e.open_base_set
  open_target := ((map_continuous f).isOpen_preimage _ e.open_baseSet).Prod isOpen_univ
  open_baseSet := (map_continuous f).isOpen_preimage _ e.open_baseSet
  continuous_toFun :=
    (Pullback.continuous_proj F E f).ContinuousOn.Prod
      (continuous_snd.comp_continuousOn <|
        e.ContinuousOn.comp (Pullback.continuous_lift F E f).ContinuousOn Subset.rfl)
  continuous_invFun := by
    dsimp only
    simp_rw [(inducing_pullbackTotalSpaceEmbedding F E f).continuousOn_iff, Function.comp,
      pullback_total_space_embedding]
    refine'
      continuous_on_fst.prod
        (e.continuous_on_symm.comp ((map_continuous f).Prod_map continuous_id).ContinuousOn
          subset.rfl)
  source_eq := by dsimp only; rw [e.source_eq]; rfl
  target_eq := rfl
  proj_toFun y h := rfl
#align trivialization.pullback Trivialization.pullback
-/

#print FiberBundle.pullback /-
noncomputable instance FiberBundle.pullback [∀ x, TopologicalSpace (E x)] [FiberBundle F E]
    (f : K) : FiberBundle F ((f : B' → B) *ᵖ E)
    where
  totalSpace_mk_inducing x :=
    inducing_of_inducing_compose (Pullback.continuous_totalSpaceMk F E)
      (Pullback.continuous_lift F E f) (totalSpace_mk_inducing F E (f x))
  trivializationAtlas :=
    {ef | ∃ (e : Trivialization F (π F E)) (_ : MemTrivializationAtlas e), ef = e.Pullback f}
  trivializationAt x := (trivializationAt F E (f x)).Pullback f
  mem_baseSet_trivializationAt x := mem_baseSet_trivializationAt F E (f x)
  trivialization_mem_atlas x := ⟨trivializationAt F E (f x), by infer_instance, rfl⟩
#align fiber_bundle.pullback FiberBundle.pullback
-/

end FiberBundle

end

