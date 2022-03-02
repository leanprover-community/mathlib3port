/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Sebastien Gouezel
-/
import Mathbin.Topology.FiberBundle
import Mathbin.Topology.Algebra.Module.Basic

/-!
# Topological vector bundles

In this file we define topological vector bundles.

Let `B` be the base space. In our formalism, a topological vector bundle is by definition the type
`bundle.total_space E` where `E : B → Type*` is a function associating to
`x : B` the fiber over `x`. This type `bundle.total_space E` is just a type synonym for
`Σ (x : B), E x`, with the interest that one can put another topology than on `Σ (x : B), E x`
which has the disjoint union topology.

To have a topological vector bundle structure on `bundle.total_space E`,
one should addtionally have the following data:

* `F` should be a topological space and a module over a semiring `R`;
* There should be a topology on `bundle.total_space E`, for which the projection to `B` is
a topological fiber bundle with fiber `F` (in particular, each fiber `E x` is homeomorphic to `F`);
* For each `x`, the fiber `E x` should be a topological vector space over `R`, and the injection
from `E x` to `bundle.total_space F E` should be an embedding;
* The most important condition: around each point, there should be a bundle trivialization which
is a continuous linear equiv in the fibers.

If all these conditions are satisfied, we register the typeclass
`topological_vector_bundle R F E`. We emphasize that the data is provided by other classes, and
that the `topological_vector_bundle` class is `Prop`-valued.

The point of this formalism is that it is unbundled in the sense that the total space of the bundle
is a type with a topology, with which one can work or put further structure, and still one can
perform operations on topological vector bundles (which are yet to be formalized). For instance,
assume that `E₁ : B → Type*` and `E₂ : B → Type*` define two topological vector bundles over `R`
with fiber models `F₁` and `F₂` which are normed spaces. Then one can construct the vector bundle of
continuous linear maps from `E₁ x` to `E₂ x` with fiber `E x := (E₁ x →L[R] E₂ x)` (and with the
topology inherited from the norm-topology on `F₁ →L[R] F₂`, without the need to define the strong
topology on continuous linear maps between general topological vector spaces). Let
`vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂ (x : B)` be a type synonym for `E₁ x →L[R] E₂ x`.
Then one can endow
`bundle.total_space (vector_bundle_continuous_linear_map R F₁ E₁ F₂ E₂)`
with a topology and a topological vector bundle structure.

Similar constructions can be done for tensor products of topological vector bundles, exterior
algebras, and so on, where the topology can be defined using a norm on the fiber model if this
helps.

## Tags
Vector bundle
-/


noncomputable section

open Bundle Set

variable (R : Type _) {B : Type _} (F : Type _) (E : B → Type _) [Semiringₓ R] [∀ x, AddCommMonoidₓ (E x)]
  [∀ x, Module R (E x)] [TopologicalSpace F] [AddCommMonoidₓ F] [Module R F] [TopologicalSpace B]

section

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- Local pretrivialization for vector prebundles. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorBundle.Pretrivialization extends
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure" where
  linear : ∀, ∀ x ∈ base_set, ∀, IsLinearMap R fun y : E x => (to_fun y).2

instance : CoeFun (TopologicalVectorBundle.Pretrivialization R F E) _ :=
  ⟨fun e => e.toFun⟩

instance :
    Coe (TopologicalVectorBundle.Pretrivialization R F E) (TopologicalFiberBundle.Pretrivialization F (proj E)) :=
  ⟨TopologicalVectorBundle.Pretrivialization.toFiberBundlePretrivialization⟩

variable [TopologicalSpace (TotalSpace E)]

-- ././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure
/-- Local trivialization for vector bundles. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorBundle.Trivialization extends
  "././Mathport/Syntax/Translate/Basic.lean:1286:11: unsupported: advanced extends in structure" where
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

variable [∀ x, TopologicalSpace (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class TopologicalVectorBundle : Prop where
  total_space_mk_inducing {} : ∀ b : B, Inducing (totalSpaceMk E b)
  locally_trivial {} : ∀ b : B, ∃ e : TopologicalVectorBundle.Trivialization R F E, b ∈ e.BaseSet

variable [TopologicalVectorBundle R F E]

namespace TopologicalVectorBundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivializationAt : ∀ b : B, Trivialization R F E := fun b => Classical.some (locally_trivial R F E b)

@[simp, mfld_simps]
theorem mem_base_set_trivialization_at (b : B) : b ∈ (trivializationAt R F E b).BaseSet :=
  Classical.some_spec (locally_trivial R F E b)

@[simp, mfld_simps]
theorem mem_source_trivialization_at (z : TotalSpace E) : z ∈ (trivializationAt R F E z.1).Source := by
  rw [TopologicalFiberBundle.Trivialization.mem_source]
  apply mem_base_set_trivialization_at

variable {R F E}

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
    dsimp
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
    dsimp
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

instance TrivialBundle.topological_vector_bundle : TopologicalVectorBundle R F (Bundle.Trivial B F) where
  locally_trivial := fun x => ⟨TrivialTopologicalVectorBundle.trivialization R B F, mem_univ x⟩
  total_space_mk_inducing := fun b =>
    ⟨by
      have : (fun x : trivialₓ B F b => x) = @id F := by
        ext x
        rfl
      simp only [total_space.topological_space, induced_inf, induced_compose, Function.comp, proj, induced_const,
        top_inf_eq, trivial.proj_snd, id.def, trivial.topological_space, this, induced_id]⟩

variable {R B F}

-- Not registered as an instance because of a metavariable.
theorem is_topological_vector_bundle_is_topological_fiber_bundle : IsTopologicalFiberBundle F (proj E) := fun x =>
  ⟨(trivializationAt R F E x).toFiberBundleTrivialization, mem_base_set_trivialization_at R F E x⟩

end TopologicalVectorBundle

/-! ### Constructing topological vector bundles -/


variable (B)

/-- Analogous construction of `topological_fiber_bundle_core` for vector bundles. This
construction gives a way to construct vector bundles from a structure registering how
trivialization changes act on fibers.-/
@[nolint has_inhabited_instance]
structure TopologicalVectorBundleCore (ι : Type _) where
  BaseSet : ι → Set B
  is_open_base_set : ∀ i, IsOpen (base_set i)
  indexAt : B → ι
  mem_base_set_at : ∀ x, x ∈ base_set (index_at x)
  coordChange : ι → ι → B → F →ₗ[R] F
  coord_change_self : ∀ i, ∀, ∀ x ∈ base_set i, ∀, ∀ v, coord_change i i x v = v
  coord_change_continuous :
    ∀ i j, ContinuousOn (fun p : B × F => coord_change i j p.1 p.2) ((base_set i ∩ base_set j) ×ˢ (Univ : Set F))
  coord_change_comp :
    ∀ i j k,
      ∀,
        ∀ x ∈ base_set i ∩ base_set j ∩ base_set k,
          ∀, ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

attribute [simp, mfld_simps] TopologicalVectorBundleCore.mem_base_set_at

namespace TopologicalVectorBundleCore

variable {R B F} {ι : Type _} (Z : TopologicalVectorBundleCore R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def toTopologicalVectorBundleCore : TopologicalFiberBundleCore ι B F :=
  { Z with coordChange := fun i j b => Z.coordChange i j b }

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

end FiberInstances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : TotalSpace Z.Fiber → B :=
  Bundle.proj Z.Fiber

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
instance toTopologicalSpace : TopologicalSpace (TotalSpace Z.Fiber) :=
  TopologicalFiberBundleCore.toTopologicalSpace ι ↑Z

variable {ι} (b : B) (a : F)

@[simp, mfld_simps]
theorem coe_cord_change (i j : ι) : TopologicalFiberBundleCore.coordChange (↑Z) i j b = Z.coordChange i j b :=
  rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def localTriv (i : ι) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  { TopologicalFiberBundleCore.localTriv (↑Z) i with
    linear := fun x hx =>
      { map_add := fun v w => by
          simp' only [LinearMap.map_add] with mfld_simps,
        map_smul := fun r v => by
          simp' only [LinearMap.map_smul] with mfld_simps } }

@[simp, mfld_simps]
theorem mem_local_triv_source (i : ι) (p : TotalSpace Z.Fiber) : p ∈ (Z.localTriv i).Source ↔ p.1 ∈ Z.BaseSet i :=
  Iff.rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def localTrivAt (b : B) : TopologicalVectorBundle.Trivialization R F Z.Fiber :=
  Z.localTriv (Z.indexAt b)

theorem mem_source_at : (⟨b, a⟩ : TotalSpace Z.Fiber) ∈ (Z.localTrivAt b).Source := by
  rw [local_triv_at, mem_local_triv_source]
  exact Z.mem_base_set_at b

@[simp, mfld_simps]
theorem local_triv_at_apply : (Z.localTrivAt b) ⟨b, a⟩ = ⟨b, a⟩ :=
  TopologicalFiberBundleCore.local_triv_at_apply Z b a

instance : TopologicalVectorBundle R F Z.Fiber where
  total_space_mk_inducing := fun b =>
    ⟨by
      refine' le_antisymmₓ _ fun s h => _
      · rw [← continuous_iff_le_induced]
        exact TopologicalFiberBundleCore.continuous_total_space_mk (↑Z) b
        
      · refine'
          is_open_induced_iff.mpr
            ⟨(Z.local_triv_at b).Source ∩ Z.local_triv_at b ⁻¹' ((Z.local_triv_at b).BaseSet ×ˢ s),
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
  locally_trivial := fun b => ⟨Z.localTrivAt b, Z.mem_base_set_at b⟩

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  TopologicalFiberBundleCore.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  TopologicalFiberBundleCore.is_open_map_proj Z

end TopologicalVectorBundleCore

end

section

/-! ### Topological vector prebundle -/


variable [∀ x, TopologicalSpace (E x)]

open TopologicalSpace

/-- This structure permits to define a vector bundle when trivializations are given as local
equivalences but there is not yet a topology on the total space. The total space is hence given a
topology in such a way that there is a fiber bundle structure for which the local equivalences
are also local homeomorphism and hence vector bundle trivializations. -/
@[nolint has_inhabited_instance]
structure TopologicalVectorPrebundle where
  pretrivializationAt : B → TopologicalVectorBundle.Pretrivialization R F E
  mem_base_pretrivialization_at : ∀ x : B, x ∈ (pretrivialization_at x).BaseSet
  continuous_triv_change :
    ∀ x y : B,
      ContinuousOn (pretrivialization_at x ∘ (pretrivialization_at y).toLocalEquiv.symm)
        ((pretrivialization_at y).Target ∩
          (pretrivialization_at y).toLocalEquiv.symm ⁻¹' (pretrivialization_at x).Source)
  total_space_mk_inducing : ∀ b : B, Inducing (pretrivialization_at b ∘ totalSpaceMk E b)

namespace TopologicalVectorPrebundle

variable {R E F}

/-- Natural identification of `topological_vector_prebundle` as a `topological_fiber_prebundle`. -/
def toTopologicalFiberPrebundle (a : TopologicalVectorPrebundle R F E) : TopologicalFiberPrebundle F (proj E) :=
  { a with pretrivializationAt := fun x => a.pretrivializationAt x }

/-- Topology on the total space that will make the prebundle into a bundle. -/
def totalSpaceTopology (a : TopologicalVectorPrebundle R F E) : TopologicalSpace (TotalSpace E) :=
  a.toTopologicalFiberPrebundle.totalSpaceTopology

/-- Promotion from a `topologial_vector_prebundle.trivialization` to a
  `topological_vector_bundle.trivialization`. -/
def trivializationAt (a : TopologicalVectorPrebundle R F E) (x : B) :
    @TopologicalVectorBundle.Trivialization R _ F E _ _ _ _ _ _ _ a.totalSpaceTopology := by
  let this' := a.total_space_topology
  exact { a.to_topological_fiber_prebundle.trivialization_at x with linear := (a.pretrivialization_at x).linear }

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
  let this' := a.total_space_topology
  rw
    [(a.trivialization_at b).toLocalHomeomorph.continuous_iff_continuous_comp_left (a.total_space_mk_preimage_source b)]
  exact continuous_iff_le_induced.mpr (le_antisymm_iff.mp (a.total_space_mk_inducing b).induced).1

theorem inducing_total_space_mk_of_inducing_comp (b : B) (h : Inducing (a.trivializationAt b ∘ totalSpaceMk E b)) :
    @Inducing _ _ _ a.totalSpaceTopology (totalSpaceMk E b) := by
  let this' := a.total_space_topology
  rw [← restrict_comp_cod_restrict (a.mem_trivialization_at_source b)] at h
  apply Inducing.of_cod_restrict (a.mem_trivialization_at_source b)
  refine'
    inducing_of_inducing_compose _ (continuous_on_iff_continuous_restrict.mp (a.trivialization_at b).continuous_to_fun)
      h
  exact (a.continuous_total_space_mk b).codRestrict (a.mem_trivialization_at_source b)

theorem to_topological_vector_bundle : @TopologicalVectorBundle R _ F E _ _ _ _ _ _ _ a.totalSpaceTopology _ :=
  { total_space_mk_inducing := fun b => a.inducing_total_space_mk_of_inducing_comp b (a.total_space_mk_inducing b),
    locally_trivial := fun b => ⟨a.trivializationAt b, a.mem_base_pretrivialization_at b⟩ }

end TopologicalVectorPrebundle

end

