/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel, Heather Macbeth, Patrick Massot
-/
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.Topology.FiberBundle

/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`, one should
additionally have the following data:

* `F` should be a normed space over a normed field `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* There should be a distinguished set of bundle trivializations (which are continuous linear equivs
in the fibres), the "trivialization atlas"
* There should be a choice of bundle trivialization at each point, which belongs to this atlas.

If all these conditions are satisfied, and if moreover for any two trivializations `e`, `e'` in the
atlas the transition function considered as a map from `B` into `F →L[R] F` is continuous on
`e.base_set ∩ e'.base_set` with respect to the operator norm topology on `F →L[R] F`, we register
the typeclass `topological_vector_bundle R F E`.

If `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R` with fiber
models `F₁` and `F₂`, denote by `E₁ ×ᵇ E₂` the sigma type of direct sums, with fiber
`E x := (E₁ x × E₂ x)`. We can endow `bundle.total_space (E₁ ×ᵇ E₂)` with a topological vector
bundle structure, `bundle.prod.topological_vector_bundle`.

A similar construction (which is yet to be formalized) can be done for the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber a type synonym
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces).  Likewise for tensor
products of topological vector bundles, exterior algebras, and so on, where the topology can be
defined using a norm on the fiber model if this helps.

## Tags
Vector bundle
-/


noncomputable section

open Bundle Set

variable (R : Type _) {B : Type _} (F : Type _) (E : B → Type _)

section TopologicalVectorSpace

variable [Semiringₓ R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [TopologicalSpace F] [AddCommMonoidₓ F]
  [Module R F] [TopologicalSpace B]

-- ././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure
/-- Local pretrivialization for vector prebundles. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorBundle.Pretrivialization extends
  "././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure" where
  linear : ∀, ∀ x ∈ base_set, ∀, IsLinearMap R fun y : E x => (to_fun y).2

instance : CoeFun (TopologicalVectorBundle.Pretrivialization R F E) _ :=
  ⟨fun e => e.toFun⟩

instance :
    Coe (TopologicalVectorBundle.Pretrivialization R F E) (TopologicalFiberBundle.Pretrivialization F (proj E)) :=
  ⟨TopologicalVectorBundle.Pretrivialization.toFiberBundlePretrivialization⟩

variable [TopologicalSpace (TotalSpace E)]

-- ././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure
/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorBundle.Trivialization extends
  "././Mathport/Syntax/Translate/Basic.lean:1278:11: unsupported: advanced extends in structure" where
  linear : ∀, ∀ x ∈ base_set, ∀, IsLinearMap R fun y : E x => (to_fun y).2

open TopologicalVectorBundle

instance : CoeFun (Trivialization R F E) fun _ => TotalSpace E → B × F :=
  ⟨fun e => e.toFun⟩

instance : Coe (Trivialization R F E) (TopologicalFiberBundle.Trivialization F (proj E)) :=
  ⟨TopologicalVectorBundle.Trivialization.toFiberBundleTrivialization⟩

namespace TopologicalVectorBundle

variable {R F E}

/-- Natural identification as `topological_vector_bundle.pretrivialization`. -/
def Trivialization.toPretrivialization (e : Trivialization R F E) : TopologicalVectorBundle.Pretrivialization R F E :=
  { e with }

theorem Trivialization.mem_source (e : Trivialization R F E) {x : TotalSpace E} : x ∈ e.Source ↔ proj E x ∈ e.BaseSet :=
  TopologicalFiberBundle.Trivialization.mem_source e

@[simp, mfld_simps]
theorem Trivialization.coe_coe (e : Trivialization R F E) : ⇑e.toLocalHomeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem Trivialization.coe_fst (e : Trivialization R F E) {x : TotalSpace E} (ex : x ∈ e.Source) :
    (e x).1 = (proj E) x :=
  e.proj_to_fun x ex

end TopologicalVectorBundle

end TopologicalVectorSpace

section

open TopologicalVectorBundle

variable (B)

variable [NondiscreteNormedField R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [NormedGroup F] [NormedSpace R F]
  [TopologicalSpace B] [TopologicalSpace (TotalSpace E)] [∀ x, TopologicalSpace (E x)]

/-- The valid transition functions for a topological vector bundle over `B` modelled on
a normed space `F`: a transition function must be a local homeomorphism of `B × F` with source and
target both `s ×ˢ univ`, which on this set is of the form `λ (b, v), (b, ε b v)` for some continuous
map `ε` from `s` to `F ≃L[R] F`.  Here continuity is with respect to the operator norm on
`F →L[R] F`. -/
def ContinuousTransitions (e : LocalEquiv (B × F) (B × F)) : Prop :=
  ∃ s : Set B,
    e.Source = s ×ˢ (Univ : Set F) ∧
      e.Target = s ×ˢ (Univ : Set F) ∧
        ∃ ε : B → F ≃L[R] F, ContinuousOn (fun b => (ε b : F →L[R] F)) s ∧ ∀, ∀ b ∈ s, ∀, ∀ v : F, e (b, v) = (b, ε b v)

variable {B}

-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`total_space_mk_inducing] []
-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`TrivializationAtlas] []
-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`trivializationAt] []
-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`mem_base_set_trivialization_at] []
-- ././Mathport/Syntax/Translate/Basic.lean:1250:30: infer kinds are unsupported in Lean 4: #[`trivialization_mem_atlas] []
-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (e e' «expr ∈ » trivialization_atlas)
/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class TopologicalVectorBundle where
  total_space_mk_inducing : ∀ b : B, Inducing (totalSpaceMk E b)
  TrivializationAtlas : Set (Trivialization R F E)
  trivializationAt : B → Trivialization R F E
  mem_base_set_trivialization_at : ∀ b : B, b ∈ (trivialization_at b).BaseSet
  trivialization_mem_atlas : ∀ b : B, trivialization_at b ∈ trivialization_atlas
  continuous_coord_change :
    ∀ e e' _ : e ∈ trivialization_atlas _ : e' ∈ trivialization_atlas,
      ContinuousTransitions R B F (e.toLocalEquiv.symm.trans e'.toLocalEquiv : _)

export
  TopologicalVectorBundle (TrivializationAtlas trivializationAt mem_base_set_trivialization_at trivialization_mem_atlas)

variable [TopologicalVectorBundle R F E]

namespace TopologicalVectorBundle

@[simp, mfld_simps]
theorem mem_source_trivialization_at (z : TotalSpace E) : z ∈ (trivializationAt R F E z.1).Source := by
  rw [TopologicalFiberBundle.Trivialization.mem_source]
  apply mem_base_set_trivialization_at

variable {R F E}

/-- The co-ordinate change (transition function) between two trivializations of a vector bundle
over `B` modelled on `F`: this is a function from `B` to `F ≃L[R] F` (of course, only meaningful
on the intersection of the domains of definition of the two trivializations). -/
def coordChange {e e' : Trivialization R F E} (he : e ∈ TrivializationAtlas R F E)
    (he' : e' ∈ TrivializationAtlas R F E) : B → F ≃L[R] F :=
  (TopologicalVectorBundle.continuous_coord_change e he e' he').some_spec.2.2.some

theorem continuous_on_coord_change {e e' : Trivialization R F E} (he : e ∈ TrivializationAtlas R F E)
    (he' : e' ∈ TrivializationAtlas R F E) :
    ContinuousOn (fun b => (coordChange he he' b : F →L[R] F)) (e.BaseSet ∩ e'.BaseSet) := by
  let s := (continuous_coord_change e he e' he').some
  let hs := (continuous_coord_change e he e' he').some_spec.1
  have hs : s = e.base_set ∩ e'.base_set := by
    have : s ×ˢ (univ : Set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : Set F) :=
      hs.symm.trans (TopologicalFiberBundle.Trivialization.symm_trans_source_eq e e')
    have hF : (univ : Set F).Nonempty := univ_nonempty
    rwa [prod_eq_iff_eq hF] at this
  rw [← hs]
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.1

theorem trans_eq_coord_change {e e' : Trivialization R F E} (he : e ∈ TrivializationAtlas R F E)
    (he' : e' ∈ TrivializationAtlas R F E) {b : B} (hb : b ∈ e.BaseSet ∩ e'.BaseSet) (v : F) :
    e' (e.toLocalHomeomorph.symm (b, v)) = (b, coordChange he he' b v) := by
  let s := (continuous_coord_change e he e' he').some
  let hs := (continuous_coord_change e he e' he').some_spec.1
  have hs : s = e.base_set ∩ e'.base_set := by
    have : s ×ˢ (univ : Set F) = (e.base_set ∩ e'.base_set) ×ˢ (univ : Set F) :=
      hs.symm.trans (TopologicalFiberBundle.Trivialization.symm_trans_source_eq e e')
    have hF : (univ : Set F).Nonempty := univ_nonempty
    rwa [prod_eq_iff_eq hF] at this
  rw [← hs] at hb
  exact (continuous_coord_change e he e' he').some_spec.2.2.some_spec.2 b hb v

namespace Trivialization

/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def continuousLinearEquivAt (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) : E b ≃L[R] F where
  toFun := fun y => (e ⟨b, y⟩).2
  invFun := fun z => by
    have : (e.to_local_homeomorph.symm (b, z)).fst = b := TopologicalFiberBundle.Trivialization.proj_symm_apply' _ hb
    have C : E (e.to_local_homeomorph.symm (b, z)).fst = E b := by
      rw [this]
    exact cast C (e.to_local_homeomorph.symm (b, z)).2
  left_inv := by
    intro v
    rw [← heq_iff_eq]
    apply (cast_heq _ _).trans
    have A : (b, (e ⟨b, v⟩).snd) = e ⟨b, v⟩ := by
      refine' Prod.extₓ _ rfl
      symm
      exact TopologicalFiberBundle.Trivialization.coe_fst' _ hb
    have B : e.to_local_homeomorph.symm (e ⟨b, v⟩) = ⟨b, v⟩ := by
      apply LocalHomeomorph.left_inv_on
      rw [TopologicalFiberBundle.Trivialization.mem_source]
      exact hb
    rw [A, B]
  right_inv := by
    intro v
    have B : e (e.to_local_homeomorph.symm (b, v)) = (b, v) := by
      apply LocalHomeomorph.right_inv_on
      rw [TopologicalFiberBundle.Trivialization.mem_target]
      exact hb
    have C : (e (e.to_local_homeomorph.symm (b, v))).2 = v := by
      rw [B]
    conv_rhs => rw [← C]
    dsimp'
    congr
    ext
    · exact (TopologicalFiberBundle.Trivialization.proj_symm_apply' _ hb).symm
      
    · exact
        (cast_heq _ _).trans
          (by
            rfl)
      
  map_add' := fun v w => (e.linear _ hb).map_add v w
  map_smul' := fun c v => (e.linear _ hb).map_smul c v
  continuous_to_fun := by
    refine' continuous_snd.comp _
    apply
      ContinuousOn.comp_continuous e.to_local_homeomorph.continuous_on
        (TopologicalVectorBundle.total_space_mk_inducing R F E b).Continuous fun x => _
    rw [TopologicalFiberBundle.Trivialization.mem_source]
    exact hb
  continuous_inv_fun := by
    rw [(TopologicalVectorBundle.total_space_mk_inducing R F E b).continuous_iff]
    dsimp'
    have : Continuous fun z : F => e.to_fiber_bundle_trivialization.to_local_homeomorph.symm (b, z) := by
      apply
        e.to_local_homeomorph.symm.continuous_on.comp_continuous (continuous_const.prod_mk continuous_id') fun z => _
      simp only [TopologicalFiberBundle.Trivialization.mem_target, hb, LocalEquiv.symm_source,
        LocalHomeomorph.symm_to_local_equiv]
    convert this
    ext z
    · exact (TopologicalFiberBundle.Trivialization.proj_symm_apply' _ hb).symm
      
    · exact cast_heq _ _
      

@[simp]
theorem continuous_linear_equiv_at_apply (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) (y : E b) :
    e.continuousLinearEquivAt b hb y = (e ⟨b, y⟩).2 :=
  rfl

@[simp]
theorem continuous_linear_equiv_at_apply' (e : Trivialization R F E) (x : TotalSpace E) (hx : x ∈ e.Source) :
    e.continuousLinearEquivAt (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 := by
  cases x
  rfl

theorem apply_eq_prod_continuous_linear_equiv_at (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet) (z : E b) :
    e.toLocalHomeomorph ⟨b, z⟩ = (b, e.continuousLinearEquivAt b hb z) := by
  ext
  · convert e.coe_fst _
    rw [e.source_eq]
    exact hb
    
  · simp
    

theorem symm_apply_eq_mk_continuous_linear_equiv_at_symm (e : Trivialization R F E) (b : B) (hb : b ∈ e.BaseSet)
    (z : F) : e.toLocalHomeomorph.symm ⟨b, z⟩ = totalSpaceMk E b ((e.continuousLinearEquivAt b hb).symm z) := by
  have h : (b, z) ∈ e.to_local_homeomorph.target := by
    rw [e.target_eq]
    exact ⟨hb, mem_univ _⟩
  apply e.to_local_homeomorph.inj_on (e.to_local_homeomorph.map_target h)
  · simp [e.source_eq, hb]
    
  simp [-continuous_linear_equiv_at_apply, e.apply_eq_prod_continuous_linear_equiv_at b hb,
    e.to_local_homeomorph.right_inv h]

theorem comp_continuous_linear_equiv_at_eq_coord_change {e e' : Trivialization R F E}
    (he : e ∈ TrivializationAtlas R F E) (he' : e' ∈ TrivializationAtlas R F E) {b : B}
    (hb : b ∈ e.BaseSet ∩ e'.BaseSet) :
    (e.continuousLinearEquivAt b hb.1).symm.trans (e'.continuousLinearEquivAt b hb.2) = coordChange he he' b := by
  ext v
  suffices
    (b, e'.continuous_linear_equiv_at b hb.2 ((e.continuous_linear_equiv_at b hb.1).symm v)) =
      (b, coord_change he he' b v)
    by
    simpa using this
  rw [← trans_eq_coord_change he he' hb, ← apply_eq_prod_continuous_linear_equiv_at,
    symm_apply_eq_mk_continuous_linear_equiv_at_symm]
  rfl

end Trivialization

section

attribute [local reducible] Bundle.Trivial

instance {B : Type _} {F : Type _} [AddCommMonoidₓ F] (b : B) : AddCommMonoidₓ (Bundle.Trivial B F b) :=
  ‹AddCommMonoidₓ F›

instance {B : Type _} {F : Type _} [AddCommGroupₓ F] (b : B) : AddCommGroupₓ (Bundle.Trivial B F b) :=
  ‹AddCommGroupₓ F›

instance {B : Type _} {F : Type _} [AddCommMonoidₓ F] [Module R F] (b : B) : Module R (Bundle.Trivial B F b) :=
  ‹Module R F›

end

variable (R B F)

/-- Local trivialization for trivial bundle. -/
def TrivialTopologicalVectorBundle.trivialization : Trivialization R F (Bundle.Trivial B F) where
  toFun := fun x => (x.fst, x.snd)
  invFun := fun y => ⟨y.fst, y.snd⟩
  Source := Univ
  Target := Univ
  map_source' := fun x h => mem_univ (x.fst, x.snd)
  map_target' := fun y h => mem_univ ⟨y.fst, y.snd⟩
  left_inv' := fun x h => Sigma.eq rfl rfl
  right_inv' := fun x h => Prod.extₓ rfl rfl
  open_source := is_open_univ
  open_target := is_open_univ
  continuous_to_fun := by
    rw [← continuous_iff_continuous_on_univ, continuous_iff_le_induced]
    simp only [Prod.topologicalSpace, induced_inf, induced_compose]
    exact le_rfl
  continuous_inv_fun := by
    rw [← continuous_iff_continuous_on_univ, continuous_iff_le_induced]
    simp only [Bundle.TotalSpace.topologicalSpace, induced_inf, induced_compose]
    exact le_rfl
  BaseSet := Univ
  open_base_set := is_open_univ
  source_eq := rfl
  target_eq := by
    simp only [univ_prod_univ]
  proj_to_fun := fun y hy => rfl
  linear := fun x hx => ⟨fun y z => rfl, fun c y => rfl⟩

@[simp]
theorem TrivialTopologicalVectorBundle.trivialization_source :
    (TrivialTopologicalVectorBundle.trivialization R B F).Source = univ :=
  rfl

@[simp]
theorem TrivialTopologicalVectorBundle.trivialization_target :
    (TrivialTopologicalVectorBundle.trivialization R B F).Target = univ :=
  rfl

instance TrivialBundle.topologicalVectorBundle : TopologicalVectorBundle R F (Bundle.Trivial B F) where
  TrivializationAtlas := {TrivialTopologicalVectorBundle.trivialization R B F}
  trivializationAt := fun x => TrivialTopologicalVectorBundle.trivialization R B F
  mem_base_set_trivialization_at := mem_univ
  trivialization_mem_atlas := fun x => mem_singleton _
  total_space_mk_inducing := fun b =>
    ⟨by
      have : (fun x : trivialₓ B F b => x) = @id F := by
        ext x
        rfl
      simp only [total_space.topological_space, induced_inf, induced_compose, Function.comp, proj, induced_const,
        top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this, induced_id]⟩
  continuous_coord_change := by
    intro e he e' he'
    rw [mem_singleton_iff.mp he, mem_singleton_iff.mp he']
    exact
      ⟨univ, by
        simp , by
        simp , fun b => ContinuousLinearEquiv.refl R F, continuous_const.continuous_on, fun b hb v => rfl⟩

variable {R B F}

-- Not registered as an instance because of a metavariable.
theorem is_topological_vector_bundle_is_topological_fiber_bundle : IsTopologicalFiberBundle F (proj E) := fun x =>
  ⟨(trivializationAt R F E x).toFiberBundleTrivialization, mem_base_set_trivialization_at R F E x⟩

variable (R B F)

include R F

@[continuity]
theorem continuous_proj : Continuous (proj E) := by
  apply @IsTopologicalFiberBundle.continuous_proj B F
  apply @is_topological_vector_bundle_is_topological_fiber_bundle R

end TopologicalVectorBundle

/-! ### Constructing topological vector bundles -/


variable (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers. -/
structure TopologicalVectorBundleCore (ι : Type _) where
  BaseSet : ι → Set B
  is_open_base_set : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_base_set_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F →L[R] F
  coord_change_self : ∀ i, ∀, ∀ x ∈ base_set i, ∀, ∀ v, coord_change i i x v = v
  coord_change_continuous : ∀ i j, ContinuousOn (coord_change i j) (base_set i ∩ base_set j)
  coord_change_comp :
    ∀ i j k,
      ∀,
        ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
          ∀, ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

/-- The trivial topological vector bundle core, in which all the changes of coordinates are the
identity. -/
def trivialTopologicalVectorBundleCore (ι : Type _) [Inhabited ι] : TopologicalVectorBundleCore R B F ι where
  BaseSet := fun ι => Univ
  is_open_base_set := fun i => is_open_univ
  indexAt := fun x => default
  mem_base_set_at := fun x => mem_univ x
  coordChange := fun i j x => ContinuousLinearMap.id R F
  coord_change_self := fun i x hx v => rfl
  coord_change_comp := fun i j k x hx v => rfl
  coord_change_continuous := fun i j => continuous_on_const

instance (ι : Type _) [Inhabited ι] : Inhabited (TopologicalVectorBundleCore R B F ι) :=
  ⟨trivialTopologicalVectorBundleCore R B F ι⟩

namespace TopologicalVectorBundleCore

variable {R B F} {ι : Type _} (Z : TopologicalVectorBundleCore R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def toTopologicalVectorBundleCore : TopologicalFiberBundleCore ι B F :=
  { Z with coordChange := fun i j b => Z.coordChange i j b,
    coord_change_continuous := fun i j =>
      is_bounded_bilinear_map_apply.Continuous.comp_continuous_on
        ((Z.coord_change_continuous i j).prod_map continuous_on_id) }

instance toTopologicalVectorBundleCoreCoe :
    Coe (TopologicalVectorBundleCore R B F ι) (TopologicalFiberBundleCore ι B F) :=
  ⟨toTopologicalVectorBundleCore⟩

include Z

theorem coord_change_linear_comp (i j k : ι) :
    ∀,
      ∀ x ∈ Z.BaseSet i ∩ Z.BaseSet j ∩ Z.BaseSet k,
        ∀, (Z.coordChange j k x).comp (Z.coordChange i j x) = Z.coordChange i k x :=
  fun x hx => by
  ext v
  exact Z.coord_change_comp i j k x hx v

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def Index :=
  ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def Base :=
  B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def Fiber (x : B) :=
  F

section FiberInstances

attribute [local reducible] fiber

--just to record instances
instance topologicalSpaceFiber (x : B) : TopologicalSpace (Z.Fiber x) := by
  infer_instance

instance addCommMonoidFiber : ∀ x : B, AddCommMonoidₓ (Z.Fiber x) := fun x => by
  infer_instance

instance moduleFiber : ∀ x : B, Module R (Z.Fiber x) := fun x => by
  infer_instance

variable [AddCommGroupₓ F]

instance addCommGroupFiber : ∀ x : B, AddCommGroupₓ (Z.Fiber x) := fun x => by
  infer_instance

end FiberInstances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : TotalSpace Z.Fiber → B :=
  Bundle.proj Z.Fiber

/-- The total space of the topological vector bundle, as a convenience function for dot notation.
It is by definition equal to `bundle.total_space Z.fiber`, a.k.a. `Σ x, Z.fiber x` but with a
different name for typeclass inference. -/
@[nolint unused_arguments, reducible]
def TotalSpace :=
  Bundle.TotalSpace Z.Fiber

/-- Local homeomorphism version of the trivialization change. -/
def trivChange (i j : ι) : LocalHomeomorph (B × F) (B × F) :=
  TopologicalFiberBundleCore.trivChange (↑Z) i j

@[simp, mfld_simps]
theorem mem_triv_change_source (i j : ι) (p : B × F) :
    p ∈ (Z.trivChange i j).Source ↔ p.1 ∈ Z.BaseSet i ∩ Z.BaseSet j :=
  TopologicalFiberBundleCore.mem_triv_change_source (↑Z) i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance toTopologicalSpace : TopologicalSpace Z.TotalSpace :=
  TopologicalFiberBundleCore.toTopologicalSpace ι ↑Z

variable {ι} (b : B) (a : F)

@[simp, mfld_simps]
theorem coe_coord_change (i j : ι) : TopologicalFiberBundleCore.coordChange (↑Z) i j b = Z.coordChange i j b :=
  rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  { TopologicalFiberBundleCore.localTriv (↑Z) i with
    linear := fun x hx =>
      { map_add := fun v w => by
          simp' only [ContinuousLinearMap.map_add] with mfld_simps,
        map_smul := fun r v => by
          simp' only [ContinuousLinearMap.map_smul] with mfld_simps } }

variable (i : ι)

@[simp, mfld_simps]
theorem mem_local_triv_source (p : Z.TotalSpace) : p ∈ (Z.localTriv i).Source ↔ p.1 ∈ Z.BaseSet i :=
  Iff.rfl

@[simp, mfld_simps]
theorem base_set_at : Z.BaseSet i = (Z.localTriv i).BaseSet :=
  rfl

@[simp, mfld_simps]
theorem local_triv_apply (p : Z.TotalSpace) : (Z.localTriv i) p = ⟨p.1, Z.coordChange (Z.indexAt p.1) i p.1 p.2⟩ :=
  rfl

@[simp, mfld_simps]
theorem mem_local_triv_target (p : B × F) : p ∈ (Z.localTriv i).Target ↔ p.1 ∈ (Z.localTriv i).BaseSet :=
  TopologicalFiberBundleCore.mem_local_triv_target Z i p

@[simp, mfld_simps]
theorem local_triv_symm_fst (p : B × F) :
    (Z.localTriv i).toLocalHomeomorph.symm p = ⟨p.1, Z.coordChange i (Z.indexAt p.1) p.1 p.2⟩ :=
  rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  Z.localTriv (Z.indexAt b)

@[simp, mfld_simps]
theorem local_triv_at_def : Z.localTriv (Z.indexAt b) = Z.localTrivAt b :=
  rfl

@[simp, mfld_simps]
theorem mem_source_at : (⟨b, a⟩ : Z.TotalSpace) ∈ (Z.localTrivAt b).Source := by
  rw [local_triv_at, mem_local_triv_source]
  exact Z.mem_base_set_at b

@[simp, mfld_simps]
theorem local_triv_at_apply : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  TopologicalFiberBundleCore.local_triv_at_apply Z b a

@[simp, mfld_simps]
theorem mem_local_triv_at_base_set : b ∈ (Z.localTrivAt b).BaseSet :=
  TopologicalFiberBundleCore.mem_local_triv_at_base_set Z b

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
instance : TopologicalVectorBundle R F Z.Fiber where
  total_space_mk_inducing := fun b =>
    ⟨by
      refine' le_antisymmₓ _ fun s h => _
      · rw [← continuous_iff_le_induced]
        exact TopologicalFiberBundleCore.continuous_total_space_mk (↑Z) b
        
      · refine'
          is_open_induced_iff.mpr
            ⟨(Z.local_triv_at b).Source ∩ Z.local_triv_at b ⁻¹' (Z.local_triv_at b).BaseSet ×ˢ s,
              (continuous_on_open_iff (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
                ((Z.local_triv_at b).open_base_set.Prod h),
              _⟩
        rw [preimage_inter, ← preimage_comp, Function.comp]
        simp only [total_space_mk]
        refine' ext_iff.mpr fun a => ⟨fun ha => _, fun ha => ⟨Z.mem_base_set_at b, _⟩⟩
        · simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply] at ha
          exact ha.2.2
          
        · simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply]
          exact ⟨Z.mem_base_set_at b, ha⟩
          
        ⟩
  TrivializationAtlas := Set.Range Z.localTriv
  trivializationAt := Z.localTrivAt
  mem_base_set_trivialization_at := Z.mem_base_set_at
  trivialization_mem_atlas := fun b => ⟨Z.indexAt b, rfl⟩
  continuous_coord_change := by
    classical
    rintro _ ⟨i, rfl⟩ _ ⟨i', rfl⟩
    refine'
      ⟨Z.base_set i ∩ Z.base_set i', _, _, fun b =>
        if h : b ∈ Z.base_set i ∩ Z.base_set i' then
          ContinuousLinearEquiv.equivOfInverse (Z.coord_change i i' b) (Z.coord_change i' i b) _ _
        else ContinuousLinearEquiv.refl R F,
        _, _⟩
    · ext ⟨b, f⟩
      simp
      
    · ext ⟨b, f⟩
      simp [and_comm]
      
    · intro f
      rw [Z.coord_change_comp _ _ _ _ ⟨h, h.1⟩, Z.coord_change_self _ _ h.1]
      
    · intro f
      rw [Z.coord_change_comp _ _ _ _ ⟨⟨h.2, h.1⟩, h.2⟩, Z.coord_change_self _ _ h.2]
      
    · apply ContinuousOn.congr (Z.coord_change_continuous i i')
      intro b hb
      simp [hb]
      ext v
      rfl
      
    · intro b hb v
      have : b ∈ Z.base_set i ∩ Z.base_set (Z.index_at b) ∩ Z.base_set i' := by
        simp only [base_set_at, local_triv_at_def, mem_inter_eq, mem_local_triv_at_base_set] at *
        tauto
      simp [hb, Z.coord_change_comp _ _ _ _ this]
      

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  TopologicalFiberBundleCore.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  TopologicalFiberBundleCore.is_open_map_proj Z

end TopologicalVectorBundleCore

end

/-! ### Topological vector prebundle -/


section

variable [NondiscreteNormedField R] [∀ x, AddCommMonoidₓ (E x)] [∀ x, Module R (E x)] [NormedGroup F] [NormedSpace R F]
  [TopologicalSpace B] [∀ x, TopologicalSpace (E x)]

open TopologicalSpace

-- ././Mathport/Syntax/Translate/Basic.lean:598:2: warning: expanding binder collection (e e' «expr ∈ » pretrivialization_atlas)
/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphisms and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorPrebundle where
  PretrivializationAtlas : Set (TopologicalVectorBundle.Pretrivialization R F E)
  pretrivializationAt : B → TopologicalVectorBundle.Pretrivialization R F E
  mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).BaseSet
  pretrivialization_mem_atlas : ∀ x : B, pretrivialization_at x ∈ pretrivialization_atlas
  continuous_coord_change :
    ∀ e e' _ : e ∈ pretrivialization_atlas _ : e' ∈ pretrivialization_atlas,
      ContinuousTransitions R B F (e'.toLocalEquiv.symm.trans e.toLocalEquiv : _)
  total_space_mk_inducing : ∀ b : B, Inducing (pretrivialization_at b ∘ totalSpaceMk E b)

namespace TopologicalVectorPrebundle

variable {R E F}

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def toTopologicalFiberPrebundle (a : TopologicalVectorPrebundle R F E) : TopologicalFiberPrebundle F (proj E) :=
  { a with PretrivializationAtlas := pretrivialization.to_fiber_bundle_pretrivialization '' a.PretrivializationAtlas,
    pretrivializationAt := fun x => (a.pretrivializationAt x).toFiberBundlePretrivialization,
    pretrivialization_mem_atlas := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩,
    continuous_triv_change := by
      rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
      obtain ⟨s, hs, hs', ε, hε, heε⟩ := a.continuous_coord_change e he e' he'
      have H :
        e'.to_fiber_bundle_pretrivialization.to_local_equiv.target ∩
            e'.to_fiber_bundle_pretrivialization.to_local_equiv.symm ⁻¹'
              e.to_fiber_bundle_pretrivialization.to_local_equiv.source =
          s ×ˢ (univ : Set F) :=
        by
        simpa using hs
      rw [H]
      have : ContinuousOn (fun p : B × F => (p.1, (ε p.1) p.2)) (s ×ˢ (univ : Set F)) := by
        apply continuous_on_fst.prod
        exact is_bounded_bilinear_map_apply.continuous.comp_continuous_on (hε.prod_map continuous_on_id)
      apply this.congr
      rintro ⟨b, f⟩ ⟨hb : b ∈ s, -⟩
      exact heε _ hb _ }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : TopologicalVectorPrebundle R F E) : TopologicalSpace (TotalSpace E) :=
  a.toTopologicalFiberPrebundle.totalSpaceTopology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivializationOfMemPretrivializationAtlas (a : TopologicalVectorPrebundle R F E)
    {e : TopologicalVectorBundle.Pretrivialization R F E} (he : e ∈ a.PretrivializationAtlas) :
    @TopologicalVectorBundle.Trivialization R _ F E _ _ _ _ _ _ _ a.totalSpaceTopology := by
  let this := a.total_space_topology
  exact
    { a.to_topological_fiber_prebundle.trivialization_of_mem_pretrivialization_atlas ⟨e, he, rfl⟩ with
      linear := e.linear }

variable (a : TopologicalVectorPrebundle R F E)

theorem mem_trivialization_at_source (b : B) (x : E b) : totalSpaceMk E b x ∈ (a.pretrivializationAt b).Source := by
  simp only [(a.pretrivialization_at b).source_eq, mem_preimage, proj]
  exact a.mem_base_pretrivialization_at b

@[simp]
theorem total_space_mk_preimage_source (b : B) : totalSpaceMk E b ⁻¹' (a.pretrivializationAt b).Source = univ := by
  apply eq_univ_of_univ_subset
  rw [(a.pretrivialization_at b).source_eq, ← preimage_comp, Function.comp]
  simp only [proj]
  rw [preimage_const_of_mem _]
  exact a.mem_base_pretrivialization_at b

@[continuity]
theorem continuous_total_space_mk (b : B) : @Continuous _ _ _ a.totalSpaceTopology (totalSpaceMk E b) := by
  let this := a.total_space_topology
  let e := a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas b)
  rw [e.to_local_homeomorph.continuous_iff_continuous_comp_left (a.total_space_mk_preimage_source b)]
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1

theorem inducing_total_space_mk_of_inducing_comp (b : B) (h : Inducing (a.pretrivializationAt b ∘ totalSpaceMk E b)) :
    @Inducing _ _ _ a.totalSpaceTopology (totalSpaceMk E b) := by
  let this := a.total_space_topology
  rw [← restrict_comp_cod_restrict (a.mem_trivialization_at_source b)] at h
  apply Inducing.of_cod_restrict (a.mem_trivialization_at_source b)
  refine'
    inducing_of_inducing_compose _
      (continuous_on_iff_continuous_restrict.mp
        (a.trivialization_of_mem_pretrivialization_atlas (a.pretrivialization_mem_atlas b)).continuous_to_fun)
      h
  exact (a.continuous_total_space_mk b).codRestrict (a.mem_trivialization_at_source b)

/-- Make a `topological_vector_bundle` from a `topological_vector_prebundle`.  Concretely this means
that, given a `topological_vector_prebundle` structure for a sigma-type `E` -- which consists of a
number of "pretrivializations" identifying parts of `E` with product spaces `U × F` -- one
establishes that for the topology constructed on the sigma-type using
`topological_vector_prebundle.total_space_topology`, these "pretrivializations" are actually
"trivializations" (i.e., homeomorphisms with respect to the constructed topology). -/
def toTopologicalVectorBundle : @TopologicalVectorBundle R _ F E _ _ _ _ _ _ a.totalSpaceTopology _ where
  total_space_mk_inducing := fun b => a.inducing_total_space_mk_of_inducing_comp b (a.total_space_mk_inducing b)
  TrivializationAtlas :=
    { e | ∃ (e₀ : _)(he₀ : e₀ ∈ a.PretrivializationAtlas), e = a.trivializationOfMemPretrivializationAtlas he₀ }
  trivializationAt := fun x => a.trivializationOfMemPretrivializationAtlas (a.pretrivialization_mem_atlas x)
  mem_base_set_trivialization_at := a.mem_base_pretrivialization_at
  trivialization_mem_atlas := fun x => ⟨_, a.pretrivialization_mem_atlas x, rfl⟩
  continuous_coord_change := by
    rintro _ ⟨e, he, rfl⟩ _ ⟨e', he', rfl⟩
    exact a.continuous_coord_change e' he' e he

end TopologicalVectorPrebundle

end

/-! ### Direct sum of two vector bundles over the same base -/


namespace TopologicalVectorBundle

section Defs

variable (E₁ : B → Type _) (E₂ : B → Type _)

variable [TopologicalSpace (TotalSpace E₁)] [TopologicalSpace (TotalSpace E₂)]

/-- Equip the total space of the fibrewise product of two topological vector bundles `E₁`, `E₂` with
the induced topology from the diagonal embedding into `(total_space E₁) × (total_space E₂)`. -/
instance Prod.topologicalSpace : TopologicalSpace (TotalSpace (E₁×ᵇE₂)) :=
  TopologicalSpace.induced (fun p => ((⟨p.1, p.2.1⟩ : TotalSpace E₁), (⟨p.1, p.2.2⟩ : TotalSpace E₂)))
    (by
      infer_instance : TopologicalSpace (TotalSpace E₁ × TotalSpace E₂))

/-- The diagonal map from the total space of the fibrewise product of two topological vector bundles
`E₁`, `E₂` into `(total_space E₁) × (total_space E₂)` is `inducing`. -/
theorem Prod.inducing_diag :
    Inducing (fun p => (⟨p.1, p.2.1⟩, ⟨p.1, p.2.2⟩) : TotalSpace (E₁×ᵇE₂) → TotalSpace E₁ × TotalSpace E₂) :=
  ⟨rfl⟩

end Defs

variable [NondiscreteNormedField R] [TopologicalSpace B]

variable (F₁ : Type _) [NormedGroup F₁] [NormedSpace R F₁] (E₁ : B → Type _) [TopologicalSpace (TotalSpace E₁)]
  [∀ x, AddCommMonoidₓ (E₁ x)] [∀ x, Module R (E₁ x)]

variable (F₂ : Type _) [NormedGroup F₂] [NormedSpace R F₂] (E₂ : B → Type _) [TopologicalSpace (TotalSpace E₂)]
  [∀ x, AddCommMonoidₓ (E₂ x)] [∀ x, Module R (E₂ x)]

namespace Trivialization

variable (e₁ : Trivialization R F₁ E₁) (e₂ : Trivialization R F₂ E₂)

include e₁ e₂

variable {R F₁ E₁ F₂ E₂}

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the forward
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def Prod.toFun' : TotalSpace (E₁×ᵇE₂) → B × F₁ × F₂ := fun ⟨x, v₁, v₂⟩ => ⟨x, (e₁ ⟨x, v₁⟩).2, (e₂ ⟨x, v₂⟩).2⟩

variable {e₁ e₂}

theorem Prod.continuous_to_fun : ContinuousOn (Prod.toFun' e₁ e₂) (proj (E₁×ᵇE₂) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)) := by
  let f₁ : total_space (E₁×ᵇE₂) → total_space E₁ × total_space E₂ := fun p =>
    ((⟨p.1, p.2.1⟩ : total_space E₁), (⟨p.1, p.2.2⟩ : total_space E₂))
  let f₂ : total_space E₁ × total_space E₂ → (B × F₁) × B × F₂ := fun p => ⟨e₁ p.1, e₂ p.2⟩
  let f₃ : (B × F₁) × B × F₂ → B × F₁ × F₂ := fun p => ⟨p.1.1, p.1.2, p.2.2⟩
  have hf₁ : Continuous f₁ := (prod.inducing_diag E₁ E₂).Continuous
  have hf₂ : ContinuousOn f₂ (e₁.source ×ˢ e₂.source) :=
    e₁.to_local_homeomorph.continuous_on.prod_map e₂.to_local_homeomorph.continuous_on
  have hf₃ : Continuous f₃ := (continuous_fst.comp continuous_fst).prod_mk (continuous_snd.prod_map continuous_snd)
  refine' ((hf₃.comp_continuous_on hf₂).comp hf₁.continuous_on _).congr _
  · rw [e₁.source_eq, e₂.source_eq]
    exact maps_to_preimage _ _
    
  rintro ⟨b, v₁, v₂⟩ ⟨hb₁, hb₂⟩
  simp only [prod.to_fun', Prod.mk.inj_iffₓ, eq_self_iff_true, and_trueₓ]
  rw [e₁.coe_fst]
  rw [e₁.source_eq, mem_preimage]
  exact hb₁

variable (e₁ e₂)

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle R F₁ E₁]
  [TopologicalVectorBundle R F₂ E₂]

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the inverse
function for the construction `topological_vector_bundle.trivialization.prod`, the induced
trivialization for the direct sum of `E₁` and `E₂`. -/
def Prod.invFun' (p : B × F₁ × F₂) : TotalSpace (E₁×ᵇE₂) := by
  obtain ⟨x, w₁, w₂⟩ := p
  refine' ⟨x, _, _⟩
  · by_cases' h : x ∈ e₁.base_set
    · exact (e₁.continuous_linear_equiv_at x h).symm w₁
      
    · exact 0
      
    
  · by_cases' h : x ∈ e₂.base_set
    · exact (e₂.continuous_linear_equiv_at x h).symm w₂
      
    · exact 0
      
    

variable {e₁ e₂}

theorem Prod.inv_fun'_apply {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) (w₁ : F₁) (w₂ : F₂) :
    Prod.invFun' e₁ e₂ ⟨x, w₁, w₂⟩ =
      ⟨x, ((e₁.continuousLinearEquivAt x hx₁).symm w₁, (e₂.continuousLinearEquivAt x hx₂).symm w₂)⟩ :=
  by
  dsimp' [prod.inv_fun']
  rw [dif_pos, dif_pos]

theorem Prod.left_inv {x : TotalSpace (E₁×ᵇE₂)} (h : x ∈ proj (E₁×ᵇE₂) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)) :
    Prod.invFun' e₁ e₂ (Prod.toFun' e₁ e₂ x) = x := by
  obtain ⟨x, v₁, v₂⟩ := x
  simp only [prod.to_fun', prod.inv_fun', Sigma.mk.inj_iff, true_andₓ, eq_self_iff_true, Prod.mk.inj_iffₓ, heq_iff_eq]
  constructor
  · rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1, ContinuousLinearEquiv.symm_apply_apply]
    
  · rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2, ContinuousLinearEquiv.symm_apply_apply]
    

theorem Prod.right_inv {x : B × F₁ × F₂} (h : x ∈ (e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Univ : Set (F₁ × F₂))) :
    Prod.toFun' e₁ e₂ (Prod.invFun' e₁ e₂ x) = x := by
  obtain ⟨x, w₁, w₂⟩ := x
  obtain ⟨h, -⟩ := h
  dsimp' only [prod.to_fun', prod.inv_fun']
  simp only [Prod.mk.inj_iffₓ, eq_self_iff_true, true_andₓ]
  constructor
  · rw [dif_pos, ← e₁.continuous_linear_equiv_at_apply x h.1, ContinuousLinearEquiv.apply_symm_apply]
    
  · rw [dif_pos, ← e₂.continuous_linear_equiv_at_apply x h.2, ContinuousLinearEquiv.apply_symm_apply]
    

theorem Prod.continuous_inv_fun :
    ContinuousOn (Prod.invFun' e₁ e₂) ((e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Univ : Set (F₁ × F₂))) := by
  rw [(prod.inducing_diag E₁ E₂).continuous_on_iff]
  suffices
    ContinuousOn
      (fun p : B × F₁ × F₂ => (e₁.to_local_homeomorph.symm ⟨p.1, p.2.1⟩, e₂.to_local_homeomorph.symm ⟨p.1, p.2.2⟩))
      ((e₁.base_set ∩ e₂.base_set) ×ˢ (univ : Set (F₁ × F₂)))
    by
    refine' this.congr _
    rintro ⟨b, v₁, v₂⟩ ⟨⟨h₁, h₂⟩, _⟩
    dsimp'  at h₁ h₂⊢
    rw [prod.inv_fun'_apply h₁ h₂, e₁.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₁,
      e₂.symm_apply_eq_mk_continuous_linear_equiv_at_symm b h₂]
  have H₁ : Continuous fun p : B × F₁ × F₂ => ((p.1, p.2.1), (p.1, p.2.2)) :=
    (continuous_id.prod_map continuous_fst).prod_mk (continuous_id.prod_map continuous_snd)
  have H₂ := e₁.to_local_homeomorph.symm.continuous_on.prod_map e₂.to_local_homeomorph.symm.continuous_on
  refine' H₂.comp H₁.continuous_on fun x h => ⟨_, _⟩
  · dsimp'
    rw [e₁.target_eq]
    exact ⟨h.1.1, mem_univ _⟩
    
  · dsimp'
    rw [e₂.target_eq]
    exact ⟨h.1.2, mem_univ _⟩
    

variable (e₁ e₂)

/-- Given trivializations `e₁`, `e₂` for vector bundles `E₁`, `E₂` over a base `B`, the induced
trivialization for the direct sum of `E₁` and `E₂`, whose base set is `e₁.base_set ∩ e₂.base_set`.
-/
def prod : Trivialization R (F₁ × F₂) (E₁×ᵇE₂) where
  toFun := Prod.toFun' e₁ e₂
  invFun := Prod.invFun' e₁ e₂
  Source := (proj fun x => E₁ x × E₂ x) ⁻¹' (e₁.BaseSet ∩ e₂.BaseSet)
  Target := (e₁.BaseSet ∩ e₂.BaseSet) ×ˢ (Set.Univ : Set (F₁ × F₂))
  map_source' := fun h => ⟨h, Set.mem_univ _⟩
  map_target' := fun h => h.1
  left_inv' := fun x => Prod.left_inv
  right_inv' := fun x => Prod.right_inv
  open_source := by
    refine' (e₁.open_base_set.inter e₂.open_base_set).Preimage _
    have : Continuous (proj E₁) := continuous_proj R B F₁
    exact this.comp (continuous_fst.comp (prod.inducing_diag E₁ E₂).Continuous)
  open_target := (e₁.open_base_set.inter e₂.open_base_set).Prod is_open_univ
  continuous_to_fun := Prod.continuous_to_fun
  continuous_inv_fun := Prod.continuous_inv_fun
  BaseSet := e₁.BaseSet ∩ e₂.BaseSet
  open_base_set := e₁.open_base_set.inter e₂.open_base_set
  source_eq := rfl
  target_eq := rfl
  proj_to_fun := fun h => rfl
  linear := fun x ⟨h₁, h₂⟩ =>
    { map_add := fun ⟨v₁, v₂⟩ ⟨v₁', v₂'⟩ =>
        congr_arg2ₓ Prod.mk ((e₁.linear x h₁).map_add v₁ v₁') ((e₂.linear x h₂).map_add v₂ v₂'),
      map_smul := fun c ⟨v₁, v₂⟩ =>
        congr_arg2ₓ Prod.mk ((e₁.linear x h₁).map_smul c v₁) ((e₂.linear x h₂).map_smul c v₂) }

@[simp]
theorem base_set_prod : (prod e₁ e₂).BaseSet = e₁.BaseSet ∩ e₂.BaseSet :=
  rfl

variable {e₁ e₂}

theorem prod_apply {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) (v₁ : E₁ x) (v₂ : E₂ x) :
    prod e₁ e₂ ⟨x, (v₁, v₂)⟩ = ⟨x, e₁.continuousLinearEquivAt x hx₁ v₁, e₂.continuousLinearEquivAt x hx₂ v₂⟩ :=
  rfl

theorem prod_symm_apply {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) (w₁ : F₁) (w₂ : F₂) :
    (prod e₁ e₂).toLocalEquiv.symm (x, (w₁, w₂)) =
      ⟨x, ((e₁.continuousLinearEquivAt x hx₁).symm w₁, (e₂.continuousLinearEquivAt x hx₂).symm w₂)⟩ :=
  Prod.inv_fun'_apply hx₁ hx₂ w₁ w₂

end Trivialization

open Trivialization

variable [∀ x : B, TopologicalSpace (E₁ x)] [∀ x : B, TopologicalSpace (E₂ x)] [TopologicalVectorBundle R F₁ E₁]
  [TopologicalVectorBundle R F₂ E₂]

/-- The product of two vector bundles is a vector bundle. -/
instance _root_.bundle.prod.topological_vector_bundle : TopologicalVectorBundle R (F₁ × F₂) (E₁×ᵇE₂) where
  total_space_mk_inducing := fun b => by
    rw [(prod.inducing_diag E₁ E₂).inducing_iff]
    exact (total_space_mk_inducing R F₁ E₁ b).prod_mk (total_space_mk_inducing R F₂ E₂ b)
  TrivializationAtlas :=
    (fun p : Trivialization R F₁ E₁ × Trivialization R F₂ E₂ => p.1.Prod p.2) ''
      TrivializationAtlas R F₁ E₁ ×ˢ TrivializationAtlas R F₂ E₂
  trivializationAt := fun b => (trivializationAt R F₁ E₁ b).Prod (trivializationAt R F₂ E₂ b)
  mem_base_set_trivialization_at := fun b =>
    ⟨mem_base_set_trivialization_at R F₁ E₁ b, mem_base_set_trivialization_at R F₂ E₂ b⟩
  trivialization_mem_atlas := fun b =>
    ⟨(_, _), ⟨trivialization_mem_atlas R F₁ E₁ b, trivialization_mem_atlas R F₂ E₂ b⟩, rfl⟩
  continuous_coord_change := by
    rintro _ ⟨⟨e₁, e₂⟩, ⟨he₁, he₂⟩, rfl⟩ _ ⟨⟨e'₁, e'₂⟩, ⟨he'₁, he'₂⟩, rfl⟩
    let s := e₁.base_set ∩ e'₁.base_set
    let t := e₂.base_set ∩ e'₂.base_set
    let ε := coord_change he₁ he'₁
    let η := coord_change he₂ he'₂
    have fact :
      (s ∩ t) ×ˢ (univ : Set <| F₁ × F₂) =
        (e₁.base_set ∩ e₂.base_set ∩ (e'₁.base_set ∩ e'₂.base_set)) ×ˢ (univ : Set <| F₁ × F₂) :=
      by
      mfld_set_tac
    refine' ⟨s ∩ t, _, _, fun b => (ε b).Prod (η b), _, _⟩
    · rw [Fact]
      apply TopologicalFiberBundle.Trivialization.symm_trans_source_eq
      
    · rw [Fact]
      apply TopologicalFiberBundle.Trivialization.symm_trans_target_eq
      
    · have hε := (continuous_on_coord_change he₁ he'₁).mono (inter_subset_left s t)
      have hη := (continuous_on_coord_change he₂ he'₂).mono (inter_subset_right s t)
      exact hε.prod_map_equivL R hη
      
    · rintro b ⟨hbs, hbt⟩ ⟨u, v⟩
      have h : (e₁.prod e₂).toLocalHomeomorph.symm _ = _ := prod_symm_apply hbs.1 hbt.1 u v
      simp only [ε, η, h, prod_apply hbs.2 hbt.2, ← comp_continuous_linear_equiv_at_eq_coord_change he₁ he'₁ hbs, ←
        comp_continuous_linear_equiv_at_eq_coord_change he₂ he'₂ hbt, eq_self_iff_true, Function.comp_app,
        LocalEquiv.coe_trans, LocalHomeomorph.coe_coe, LocalHomeomorph.coe_coe_symm, Prod.mk.inj_iffₓ,
        TopologicalVectorBundle.Trivialization.coe_coe, true_andₓ, ContinuousLinearEquiv.prod_apply,
        ContinuousLinearEquiv.trans_apply]
      

variable {R F₁ E₁ F₂ E₂}

@[simp]
theorem Trivialization.continuous_linear_equiv_at_prod {e₁ : Trivialization R F₁ E₁} {e₂ : Trivialization R F₂ E₂}
    {x : B} (hx₁ : x ∈ e₁.BaseSet) (hx₂ : x ∈ e₂.BaseSet) :
    (e₁.Prod e₂).continuousLinearEquivAt x ⟨hx₁, hx₂⟩ =
      (e₁.continuousLinearEquivAt x hx₁).Prod (e₂.continuousLinearEquivAt x hx₂) :=
  by
  ext1
  funext v
  obtain ⟨v₁, v₂⟩ := v
  rw [(e₁.prod e₂).continuous_linear_equiv_at_apply, trivialization.prod]
  exact congr_argₓ Prod.snd (prod_apply hx₁ hx₂ v₁ v₂)

end TopologicalVectorBundle

