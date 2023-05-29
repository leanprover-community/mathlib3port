/-
Copyright © 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Floris van Doorn

! This file was ported from Lean 3 source module topology.vector_bundle.hom
! leanprover-community/mathlib commit f7ebde7ee0d1505dfccac8644ae12371aa3c1c9f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.VectorBundle.Basic
import Mathbin.Analysis.NormedSpace.OperatorNorm

/-!
# The vector bundle of continuous (semi)linear maps

We define the (topological) vector bundle of continuous (semi)linear maps between two vector bundles
over the same base.

Given bundles `E₁ E₂ : B → Type*`, normed spaces `F₁` and `F₂`, and a ring-homomorphism `σ` between
their respective scalar fields, we define `bundle.continuous_linear_map σ F₁ E₁ F₂ E₂ x` to be a
type synonym for `λ x, E₁ x →SL[σ] E₂ x`. If the `E₁` and `E₂` are vector bundles with model fibers
`F₁` and `F₂`, then this will be a vector bundle with fiber `F₁ →SL[σ] F₂`.

The topology on the total space is constructed from the trivializations for `E₁` and `E₂` and the
norm-topology on the model fiber `F₁ →SL[𝕜] F₂` using the `vector_prebundle` construction.  This is
a bit awkward because it introduces a dependence on the normed space structure of the model fibers,
rather than just their topological vector space structure; it is not clear whether this is
necessary.

Similar constructions should be possible (but are yet to be formalized) for tensor products of
topological vector bundles, exterior algebras, and so on, where again the topology can be defined
using a norm on the fiber model if this helps.

## Main Definitions

* `bundle.continuous_linear_map.vector_bundle`: continuous semilinear maps between
  vector bundles form a vector bundle.

-/


noncomputable section

open scoped Bundle

open Bundle Set ContinuousLinearMap

section Defs

variable {𝕜₁ 𝕜₂ : Type _} [NormedField 𝕜₁] [NormedField 𝕜₂]

variable (σ : 𝕜₁ →+* 𝕜₂)

variable {B : Type _}

variable (F₁ : Type _) (E₁ : B → Type _) [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)]

variable [∀ x, TopologicalSpace (E₁ x)]

variable (F₂ : Type _) (E₂ : B → Type _) [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)]

variable [∀ x, TopologicalSpace (E₂ x)]

include F₁ F₂

-- In this definition we require the scalar rings `𝕜₁` and `𝕜₂` to be normed fields, although
-- something much weaker (maybe `comm_semiring`) would suffice mathematically -- this is because of
-- a typeclass inference bug with pi-types:
-- https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/vector.20bundles.20--.20typeclass.20inference.20issue
/-- The bundle of continuous `σ`-semilinear maps between the topological vector bundles `E₁` and
`E₂`. This is a type synonym for `λ x, E₁ x →SL[σ] E₂ x`.

We intentionally add `F₁` and `F₂` as arguments to this type, so that instances on this type
(that depend on `F₁` and `F₂`) actually refer to `F₁` and `F₂`. -/
@[nolint unused_arguments]
protected def Bundle.ContinuousLinearMap (x : B) : Type _ :=
  E₁ x →SL[σ] E₂ x deriving Inhabited
#align bundle.continuous_linear_map Bundle.ContinuousLinearMap

instance Bundle.ContinuousLinearMap.addMonoidHomClass (x : B) :
    AddMonoidHomClass (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) (E₁ x) (E₂ x) := by
  delta_instance bundle.continuous_linear_map
#align bundle.continuous_linear_map.add_monoid_hom_class Bundle.ContinuousLinearMap.addMonoidHomClass

variable [∀ x, TopologicalAddGroup (E₂ x)]

instance (x : B) : TopologicalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) := by
  delta_instance bundle.continuous_linear_map

instance (x : B) : AddCommMonoid (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) := by
  delta_instance bundle.continuous_linear_map

variable [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]

instance (x : B) : Module 𝕜₂ (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂ x) := by
  delta_instance bundle.continuous_linear_map

end Defs

variable {𝕜₁ : Type _} [NontriviallyNormedField 𝕜₁] {𝕜₂ : Type _} [NontriviallyNormedField 𝕜₂]
  (σ : 𝕜₁ →+* 𝕜₂) [iσ : RingHomIsometric σ]

variable {B : Type _} [TopologicalSpace B]

variable (F₁ : Type _) [NormedAddCommGroup F₁] [NormedSpace 𝕜₁ F₁] (E₁ : B → Type _)
  [∀ x, AddCommGroup (E₁ x)] [∀ x, Module 𝕜₁ (E₁ x)] [TopologicalSpace (TotalSpace E₁)]

variable (F₂ : Type _) [NormedAddCommGroup F₂] [NormedSpace 𝕜₂ F₂] (E₂ : B → Type _)
  [∀ x, AddCommGroup (E₂ x)] [∀ x, Module 𝕜₂ (E₂ x)] [TopologicalSpace (TotalSpace E₂)]

variable {F₁ E₁ F₂ E₂} (e₁ e₁' : Trivialization F₁ (π E₁)) (e₂ e₂' : Trivialization F₂ (π E₂))

namespace Pretrivialization

/-- Assume `eᵢ` and `eᵢ'` are trivializations of the bundles `Eᵢ` over base `B` with fiber `Fᵢ`
(`i ∈ {1,2}`), then `continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂'` is the coordinate change
function between the two induced (pre)trivializations
`pretrivialization.continuous_linear_map σ e₁ e₂` and
`pretrivialization.continuous_linear_map σ e₁' e₂'` of `bundle.continuous_linear_map`. -/
def continuousLinearMapCoordChange [e₁.isLinear 𝕜₁] [e₁'.isLinear 𝕜₁] [e₂.isLinear 𝕜₂]
    [e₂'.isLinear 𝕜₂] (b : B) : (F₁ →SL[σ] F₂) →L[𝕜₂] F₁ →SL[σ] F₂ :=
  ((e₁'.coordChangeL 𝕜₁ e₁ b).symm.arrowCongrSL (e₂.coordChangeL 𝕜₂ e₂' b) :
    (F₁ →SL[σ] F₂) ≃L[𝕜₂] F₁ →SL[σ] F₂)
#align pretrivialization.continuous_linear_map_coord_change Pretrivialization.continuousLinearMapCoordChange

variable {σ e₁ e₁' e₂ e₂'}

variable [∀ x, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁]

variable [∀ x, TopologicalSpace (E₂ x)] [ita : ∀ x, TopologicalAddGroup (E₂ x)] [FiberBundle F₂ E₂]

include iσ

theorem continuousOn_continuousLinearMapCoordChange [VectorBundle 𝕜₁ F₁ E₁] [VectorBundle 𝕜₂ F₂ E₂]
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₁'] [MemTrivializationAtlas e₂]
    [MemTrivializationAtlas e₂'] :
    ContinuousOn (continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂')
      (e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) :=
  by
  have h₁ := (compSL F₁ F₂ F₂ σ (RingHom.id 𝕜₂)).Continuous
  have h₂ := (ContinuousLinearMap.flip (compSL F₁ F₁ F₂ (RingHom.id 𝕜₁) σ)).Continuous
  have h₃ := continuousOn_coordChange 𝕜₁ e₁' e₁
  have h₄ := continuousOn_coordChange 𝕜₂ e₂ e₂'
  refine' ((h₁.comp_continuous_on (h₄.mono _)).clm_comp (h₂.comp_continuous_on (h₃.mono _))).congr _
  · mfld_set_tac
  · mfld_set_tac
  · intro b hb; ext (L v)
    simp only [continuous_linear_map_coord_change, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.arrowCongrₛₗ_apply, LinearEquiv.toFun_eq_coe, coe_comp',
      ContinuousLinearEquiv.arrowCongrSL_apply, comp_apply, Function.comp, compSL_apply, flip_apply,
      ContinuousLinearEquiv.symm_symm]
#align pretrivialization.continuous_on_continuous_linear_map_coord_change Pretrivialization.continuousOn_continuousLinearMapCoordChange

omit iσ

variable (σ e₁ e₁' e₂ e₂') [e₁.isLinear 𝕜₁] [e₁'.isLinear 𝕜₁] [e₂.isLinear 𝕜₂] [e₂'.isLinear 𝕜₂]

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`,
`pretrivialization.continuous_linear_map σ e₁ e₂` is the induced pretrivialization for the
continuous `σ`-semilinear maps from `E₁` to `E₂`. That is, the map which will later become a
trivialization, after the bundle of continuous semilinear maps is equipped with the right
topological vector bundle structure. -/
def continuousLinearMap :
    Pretrivialization (F₁ →SL[σ] F₂) (π (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂))
    where
  toFun p :=
    ⟨p.1,
      ContinuousLinearMap.comp (e₂.continuousLinearMapAt 𝕜₂ p.1)
        (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩
  invFun p :=
    ⟨p.1,
      ContinuousLinearMap.comp (e₂.symmL 𝕜₂ p.1)
        (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1 : E₁ p.1 →L[𝕜₁] F₁) : E₁ p.1 →SL[σ] F₂)⟩
  source := Bundle.TotalSpace.proj ⁻¹' (e₁.baseSet ∩ e₂.baseSet)
  target := (e₁.baseSet ∩ e₂.baseSet) ×ˢ Set.univ
  map_source' := fun ⟨x, L⟩ h => ⟨h, Set.mem_univ _⟩
  map_target' := fun ⟨x, f⟩ h => h.1
  left_inv' := fun ⟨x, L⟩ ⟨h₁, h₂⟩ =>
    by
    simp_rw [Sigma.mk.inj_iff, eq_self_iff_true, heq_iff_eq, true_and_iff]
    ext v
    simp only [comp_apply, Trivialization.symmL_continuousLinearMapAt, h₁, h₂]
  right_inv' := fun ⟨x, f⟩ ⟨⟨h₁, h₂⟩, _⟩ =>
    by
    simp_rw [Prod.mk.inj_iff, eq_self_iff_true, true_and_iff]
    ext v
    simp only [comp_apply, Trivialization.continuousLinearMapAt_symmL, h₁, h₂]
  open_target := (e₁.open_baseSet.inter e₂.open_baseSet).Prod isOpen_univ
  baseSet := e₁.baseSet ∩ e₂.baseSet
  open_baseSet := e₁.open_baseSet.inter e₂.open_baseSet
  source_eq := rfl
  target_eq := rfl
  proj_toFun := fun ⟨x, f⟩ h => rfl
#align pretrivialization.continuous_linear_map Pretrivialization.continuousLinearMap

include ita

instance continuousLinearMap.isLinear [∀ x, ContinuousAdd (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)] :
    (Pretrivialization.continuousLinearMap σ e₁ e₂).isLinear 𝕜₂
    where linear x h :=
    { map_add := fun L L' =>
        show (e₂.continuousLinearMapAt 𝕜₂ x).comp ((L + L').comp (e₁.symmL 𝕜₁ x)) = _
          by
          simp_rw [add_comp, comp_add]
          rfl
      map_smul := fun c L =>
        show (e₂.continuousLinearMapAt 𝕜₂ x).comp ((c • L).comp (e₁.symmL 𝕜₁ x)) = _
          by
          simp_rw [smul_comp, comp_smulₛₗ, RingHom.id_apply]
          rfl }
#align pretrivialization.continuous_linear_map.is_linear Pretrivialization.continuousLinearMap.isLinear

omit ita

theorem continuousLinearMap_apply (p : TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :
    (continuousLinearMap σ e₁ e₂) p =
      ⟨p.1,
        ContinuousLinearMap.comp (e₂.continuousLinearMapAt 𝕜₂ p.1)
          (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
  rfl
#align pretrivialization.continuous_linear_map_apply Pretrivialization.continuousLinearMap_apply

theorem continuousLinearMap_symm_apply (p : B × (F₁ →SL[σ] F₂)) :
    (continuousLinearMap σ e₁ e₂).toLocalEquiv.symm p =
      ⟨p.1,
        ContinuousLinearMap.comp (e₂.symmL 𝕜₂ p.1)
          (p.2.comp (e₁.continuousLinearMapAt 𝕜₁ p.1 : E₁ p.1 →L[𝕜₁] F₁) : E₁ p.1 →SL[σ] F₂)⟩ :=
  rfl
#align pretrivialization.continuous_linear_map_symm_apply Pretrivialization.continuousLinearMap_symm_apply

include ita

theorem continuousLinearMap_symm_apply' {b : B} (hb : b ∈ e₁.baseSet ∩ e₂.baseSet)
    (L : F₁ →SL[σ] F₂) :
    (continuousLinearMap σ e₁ e₂).symm b L =
      (e₂.symmL 𝕜₂ b).comp (L.comp <| e₁.continuousLinearMapAt 𝕜₁ b) :=
  by rw [symm_apply]; rfl; exact hb
#align pretrivialization.continuous_linear_map_symm_apply' Pretrivialization.continuousLinearMap_symm_apply'

theorem continuousLinearMapCoordChange_apply (b : B)
    (hb : b ∈ e₁.baseSet ∩ e₂.baseSet ∩ (e₁'.baseSet ∩ e₂'.baseSet)) (L : F₁ →SL[σ] F₂) :
    continuousLinearMapCoordChange σ e₁ e₁' e₂ e₂' b L =
      (continuousLinearMap σ e₁' e₂' (totalSpaceMk b ((continuousLinearMap σ e₁ e₂).symm b L))).2 :=
  by
  ext v
  simp_rw [continuous_linear_map_coord_change, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.arrowCongrSL_apply, LinearEquiv.toFun_eq_coe,
    ContinuousLinearEquiv.arrowCongrₛₗ_apply, continuous_linear_map_apply,
    continuous_linear_map_symm_apply' σ e₁ e₂ hb.1, comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_symm, Trivialization.continuousLinearMapAt_apply,
    Trivialization.symmL_apply]
  dsimp only [total_space_mk]
  rw [e₂.coord_changeL_apply e₂', e₁'.coord_changeL_apply e₁, e₁.coe_linear_map_at_of_mem hb.1.1,
    e₂'.coe_linear_map_at_of_mem hb.2.2]
  exacts[⟨hb.2.1, hb.1.1⟩, ⟨hb.1.2, hb.2.2⟩]
#align pretrivialization.continuous_linear_map_coord_change_apply Pretrivialization.continuousLinearMapCoordChange_apply

end Pretrivialization

open Pretrivialization

variable (F₁ E₁ F₂ E₂)

variable [∀ x : B, TopologicalSpace (E₁ x)] [FiberBundle F₁ E₁] [VectorBundle 𝕜₁ F₁ E₁]

variable [∀ x : B, TopologicalSpace (E₂ x)] [FiberBundle F₂ E₂] [VectorBundle 𝕜₂ F₂ E₂]

variable [∀ x, TopologicalAddGroup (E₂ x)] [∀ x, ContinuousSMul 𝕜₂ (E₂ x)]

include iσ

/-- The continuous `σ`-semilinear maps between two topological vector bundles form a
`vector_prebundle` (this is an auxiliary construction for the
`vector_bundle` instance, in which the pretrivializations are collated but no topology
on the total space is yet provided). -/
def Bundle.ContinuousLinearMap.vectorPrebundle :
    VectorPrebundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)
    where
  pretrivializationAtlas :=
    { e |
      ∃ (e₁ : Trivialization F₁ (π E₁))(e₂ : Trivialization F₂ (π E₂))(_ :
        MemTrivializationAtlas e₁)(_ : MemTrivializationAtlas e₂),
        e = Pretrivialization.continuousLinearMap σ e₁ e₂ }
  pretrivialization_linear' := by
    rintro _ ⟨e₁, he₁, e₂, he₂, rfl⟩
    infer_instance
  pretrivializationAt x :=
    Pretrivialization.continuousLinearMap σ (trivializationAt F₁ E₁ x) (trivializationAt F₂ E₂ x)
  mem_base_pretrivializationAt x :=
    ⟨mem_baseSet_trivializationAt F₁ E₁ x, mem_baseSet_trivializationAt F₂ E₂ x⟩
  pretrivialization_mem_atlas x := ⟨trivializationAt F₁ E₁ x, trivializationAt F₂ E₂ x, _, _, rfl⟩
  exists_coord_change :=
    by
    rintro _ ⟨e₁, e₂, he₁, he₂, rfl⟩ _ ⟨e₁', e₂', he₁', he₂', rfl⟩
    skip
    exact
      ⟨continuous_linear_map_coord_change σ e₁ e₁' e₂ e₂',
        continuous_on_continuous_linear_map_coord_change,
        continuous_linear_map_coord_change_apply σ e₁ e₁' e₂ e₂'⟩
  totalSpaceMk_inducing := by
    intro b
    dsimp [Bundle.ContinuousLinearMap.topologicalSpace, Bundle.ContinuousLinearMap]
    let L₁ : E₁ b ≃L[𝕜₁] F₁ :=
      (trivialization_at F₁ E₁ b).continuousLinearEquivAt 𝕜₁ b
        (mem_base_set_trivialization_at _ _ _)
    let L₂ : E₂ b ≃L[𝕜₂] F₂ :=
      (trivialization_at F₂ E₂ b).continuousLinearEquivAt 𝕜₂ b
        (mem_base_set_trivialization_at _ _ _)
    let φ : (E₁ b →SL[σ] E₂ b) ≃L[𝕜₂] F₁ →SL[σ] F₂ := L₁.arrow_congrSL L₂
    have : Inducing fun x => (b, φ x) := inducing_const_prod.mpr φ.to_homeomorph.inducing
    convert this
    ext f
    · rfl
    ext x
    dsimp [φ, Pretrivialization.continuousLinearMap_apply]
    rw [Trivialization.linearMapAt_def_of_mem _ (mem_base_set_trivialization_at _ _ _)]
    rfl
#align bundle.continuous_linear_map.vector_prebundle Bundle.ContinuousLinearMap.vectorPrebundle

/-- Topology on the total space of the continuous `σ`-semilinear_maps between two "normable" vector
bundles over the same base. -/
instance Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).totalSpaceTopology
#align bundle.continuous_linear_map.topological_space_total_space Bundle.ContinuousLinearMap.topologicalSpaceTotalSpace

/-- The continuous `σ`-semilinear_maps between two vector bundles form a fiber bundle. -/
instance Bundle.ContinuousLinearMap.fiberBundle :
    FiberBundle (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).toFiberBundle
#align bundle.continuous_linear_map.fiber_bundle Bundle.ContinuousLinearMap.fiberBundle

/-- The continuous `σ`-semilinear_maps between two vector bundles form a vector bundle. -/
instance Bundle.ContinuousLinearMap.vectorBundle :
    VectorBundle 𝕜₂ (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) :=
  (Bundle.ContinuousLinearMap.vectorPrebundle σ F₁ E₁ F₂ E₂).to_vectorBundle
#align bundle.continuous_linear_map.vector_bundle Bundle.ContinuousLinearMap.vectorBundle

variable (e₁ e₂) [he₁ : MemTrivializationAtlas e₁] [he₂ : MemTrivializationAtlas e₂] {F₁ E₁ F₂ E₂}

include he₁ he₂

/-- Given trivializations `e₁`, `e₂` in the atlas for vector bundles `E₁`, `E₂` over a base `B`,
the induced trivialization for the continuous `σ`-semilinear maps from `E₁` to `E₂`,
whose base set is `e₁.base_set ∩ e₂.base_set`. -/
def Trivialization.continuousLinearMap :
    Trivialization (F₁ →SL[σ] F₂) (π (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :=
  VectorPrebundle.trivializationOfMemPretrivializationAtlas _ ⟨e₁, e₂, he₁, he₂, rfl⟩
#align trivialization.continuous_linear_map Trivialization.continuousLinearMap

instance Bundle.ContinuousLinearMap.memTrivializationAtlas :
    MemTrivializationAtlas
      (e₁.ContinuousLinearMap σ e₂ :
        Trivialization (F₁ →SL[σ] F₂) (π (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)))
    where out := ⟨_, ⟨e₁, e₂, by infer_instance, by infer_instance, rfl⟩, rfl⟩
#align bundle.continuous_linear_map.mem_trivialization_atlas Bundle.ContinuousLinearMap.memTrivializationAtlas

variable {e₁ e₂}

@[simp]
theorem Trivialization.baseSet_continuousLinearMap :
    (e₁.ContinuousLinearMap σ e₂).baseSet = e₁.baseSet ∩ e₂.baseSet :=
  rfl
#align trivialization.base_set_continuous_linear_map Trivialization.baseSet_continuousLinearMap

theorem Trivialization.continuousLinearMap_apply
    (p : TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :
    e₁.ContinuousLinearMap σ e₂ p =
      ⟨p.1,
        (e₂.continuousLinearMapAt 𝕜₂ p.1 : _ →L[𝕜₂] _).comp
          (p.2.comp (e₁.symmL 𝕜₁ p.1 : F₁ →L[𝕜₁] E₁ p.1) : F₁ →SL[σ] E₂ p.1)⟩ :=
  rfl
#align trivialization.continuous_linear_map_apply Trivialization.continuousLinearMap_apply

omit he₁ he₂

theorem hom_trivializationAt_apply (x₀ : B)
    (x : TotalSpace (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂)) :
    trivializationAt (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) x₀ x =
      ⟨x.1, inCoordinates F₁ E₁ F₂ E₂ x₀ x.1 x₀ x.1 x.2⟩ :=
  rfl
#align hom_trivialization_at_apply hom_trivializationAt_apply

@[simp, mfld_simps]
theorem hom_trivializationAt_source (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) x₀).source =
      π (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) ⁻¹'
        ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) :=
  rfl
#align hom_trivialization_at_source hom_trivializationAt_source

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
@[simp, mfld_simps]
theorem hom_trivializationAt_target (x₀ : B) :
    (trivializationAt (F₁ →SL[σ] F₂) (Bundle.ContinuousLinearMap σ F₁ E₁ F₂ E₂) x₀).target =
      ((trivializationAt F₁ E₁ x₀).baseSet ∩ (trivializationAt F₂ E₂ x₀).baseSet) ×ˢ Set.univ :=
  rfl
#align hom_trivialization_at_target hom_trivializationAt_target

