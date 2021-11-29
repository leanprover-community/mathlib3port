import Mathbin.Topology.FiberBundle 
import Mathbin.Topology.Algebra.Module

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


noncomputable theory

open Bundle Set

variable (R : Type _) {B : Type _} (F : Type _) (E : B → Type _) [Semiringₓ R] [∀ x, AddCommMonoidₓ (E x)]
  [∀ x, Module R (E x)] [TopologicalSpace F] [AddCommMonoidₓ F] [Module R F] [TopologicalSpace (total_space E)]
  [TopologicalSpace B]

section 

-- error in Topology.VectorBundle: ././Mathport/Syntax/Translate/Basic.lean:1004:11: unsupported: advanced extends in structure
/-- Local trivialization for vector bundles. -/
@[nolint #[ident has_inhabited_instance]]
structure topological_vector_bundle.trivializationextends to_fiber_bundle_trivialization : topological_fiber_bundle.trivialization F (proj E) :=
  (linear : ∀ x «expr ∈ » base_set, is_linear_map R (λ y : E x, (to_fun y).2))

open TopologicalVectorBundle

instance : CoeFun (trivialization R F E) fun _ => total_space E → B × F :=
  ⟨fun e => e.to_fun⟩

instance : Coe (trivialization R F E) (TopologicalFiberBundle.Trivialization F (proj E)) :=
  ⟨TopologicalVectorBundle.Trivialization.toFiberBundleTrivialization⟩

namespace TopologicalVectorBundle

variable {R F E}

theorem trivialization.mem_source (e : trivialization R F E) {x : total_space E} :
  x ∈ e.source ↔ proj E x ∈ e.base_set :=
  TopologicalFiberBundle.Trivialization.mem_source e

@[simp, mfld_simps]
theorem trivialization.coe_coe (e : trivialization R F E) : «expr⇑ » e.to_local_homeomorph = e :=
  rfl

@[simp, mfld_simps]
theorem trivialization.coe_fst (e : trivialization R F E) {x : total_space E} (ex : x ∈ e.source) :
  (e x).1 = (proj E) x :=
  e.proj_to_fun x ex

end TopologicalVectorBundle

end 

variable [∀ x, TopologicalSpace (E x)]

/-- The space `total_space E` (for `E : B → Type*` such that each `E x` is a topological vector
space) has a topological vector space structure with fiber `F` (denoted with
`topological_vector_bundle R F E`) if around every point there is a fiber bundle trivialization
which is linear in the fibers. -/
class TopologicalVectorBundle : Prop where 
  Inducing{} : ∀ b : B, Inducing fun x : E b => (id ⟨b, x⟩ : total_space E)
  locally_trivial{} : ∀ b : B, ∃ e : TopologicalVectorBundle.Trivialization R F E, b ∈ e.base_set

variable [TopologicalVectorBundle R F E]

namespace TopologicalVectorBundle

/-- `trivialization_at R F E b` is some choice of trivialization of a vector bundle whose base set
contains a given point `b`. -/
def trivialization_at : ∀ b : B, trivialization R F E :=
  fun b => Classical.some (locally_trivial R F E b)

@[simp, mfld_simps]
theorem mem_base_set_trivialization_at (b : B) : b ∈ (trivialization_at R F E b).BaseSet :=
  Classical.some_spec (locally_trivial R F E b)

@[simp, mfld_simps]
theorem mem_source_trivialization_at (z : total_space E) : z ∈ (trivialization_at R F E z.1).Source :=
  by 
    rw [TopologicalFiberBundle.Trivialization.mem_source]
    apply mem_base_set_trivialization_at

variable {R F E}

namespace Trivialization

-- error in Topology.VectorBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- In a topological vector bundle, a trivialization in the fiber (which is a priori only linear)
is in fact a continuous linear equiv between the fibers and the model fiber. -/
def continuous_linear_equiv_at
(e : trivialization R F E)
(b : B)
(hb : «expr ∈ »(b, e.base_set)) : «expr ≃L[ ] »(E b, R, F) :=
{ to_fun := λ y, (e ⟨b, y⟩).2,
  inv_fun := λ z, begin
    have [] [":", expr «expr = »((e.to_local_homeomorph.symm (b, z)).fst, b)] [":=", expr topological_fiber_bundle.trivialization.proj_symm_apply' _ hb],
    have [ident C] [":", expr «expr = »(E (e.to_local_homeomorph.symm (b, z)).fst, E b)] [],
    by rw [expr this] [],
    exact [expr cast C (e.to_local_homeomorph.symm (b, z)).2]
  end,
  left_inv := begin
    assume [binders (v)],
    rw ["[", "<-", expr heq_iff_eq, "]"] [],
    apply [expr (cast_heq _ _).trans],
    have [ident A] [":", expr «expr = »((b, (e ⟨b, v⟩).snd), e ⟨b, v⟩)] [],
    { refine [expr prod.ext _ rfl],
      symmetry,
      exact [expr topological_fiber_bundle.trivialization.coe_fst' _ hb] },
    have [ident B] [":", expr «expr = »(e.to_local_homeomorph.symm (e ⟨b, v⟩), ⟨b, v⟩)] [],
    { apply [expr local_homeomorph.left_inv_on],
      rw [expr topological_fiber_bundle.trivialization.mem_source] [],
      exact [expr hb] },
    rw ["[", expr A, ",", expr B, "]"] []
  end,
  right_inv := begin
    assume [binders (v)],
    have [ident B] [":", expr «expr = »(e (e.to_local_homeomorph.symm (b, v)), (b, v))] [],
    { apply [expr local_homeomorph.right_inv_on],
      rw [expr topological_fiber_bundle.trivialization.mem_target] [],
      exact [expr hb] },
    have [ident C] [":", expr «expr = »((e (e.to_local_homeomorph.symm (b, v))).2, v)] [],
    by rw ["[", expr B, "]"] [],
    conv_rhs [] [] { rw ["<-", expr C] },
    dsimp [] [] [] [],
    congr,
    ext [] [] [],
    { exact [expr (topological_fiber_bundle.trivialization.proj_symm_apply' _ hb).symm] },
    { exact [expr (cast_heq _ _).trans (by refl)] }
  end,
  map_add' := λ v w, (e.linear _ hb).map_add v w,
  map_smul' := λ c v, (e.linear _ hb).map_smul c v,
  continuous_to_fun := begin
    refine [expr continuous_snd.comp _],
    apply [expr continuous_on.comp_continuous e.to_local_homeomorph.continuous_on (topological_vector_bundle.inducing R F E b).continuous (λ
      x, _)],
    rw [expr topological_fiber_bundle.trivialization.mem_source] [],
    exact [expr hb]
  end,
  continuous_inv_fun := begin
    rw [expr (topological_vector_bundle.inducing R F E b).continuous_iff] [],
    dsimp [] [] [] [],
    have [] [":", expr continuous (λ z : F, e.to_fiber_bundle_trivialization.to_local_homeomorph.symm (b, z))] [],
    { apply [expr e.to_local_homeomorph.symm.continuous_on.comp_continuous (continuous_const.prod_mk continuous_id') (λ
        z, _)],
      simp [] [] ["only"] ["[", expr topological_fiber_bundle.trivialization.mem_target, ",", expr hb, ",", expr local_equiv.symm_source, ",", expr local_homeomorph.symm_to_local_equiv, "]"] [] [] },
    convert [] [expr this] [],
    ext [] [ident z] [],
    { exact [expr (topological_fiber_bundle.trivialization.proj_symm_apply' _ hb).symm] },
    { exact [expr cast_heq _ _] }
  end }

@[simp]
theorem continuous_linear_equiv_at_apply (e : trivialization R F E) (b : B) (hb : b ∈ e.base_set) (y : E b) :
  e.continuous_linear_equiv_at b hb y = (e ⟨b, y⟩).2 :=
  rfl

@[simp]
theorem continuous_linear_equiv_at_apply' (e : trivialization R F E) (x : total_space E) (hx : x ∈ e.source) :
  e.continuous_linear_equiv_at (proj E x) (e.mem_source.1 hx) x.2 = (e x).2 :=
  by 
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
def trivial_topological_vector_bundle.trivialization : trivialization R F (Bundle.Trivial B F) :=
  { toFun := fun x => (x.fst, x.snd), invFun := fun y => ⟨y.fst, y.snd⟩, Source := univ, Target := univ,
    map_source' := fun x h => mem_univ (x.fst, x.snd), map_target' := fun y h => mem_univ ⟨y.fst, y.snd⟩,
    left_inv' := fun x h => Sigma.eq rfl rfl, right_inv' := fun x h => Prod.extₓ rfl rfl, open_source := is_open_univ,
    open_target := is_open_univ,
    continuous_to_fun :=
      by 
        rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced]
        simp only [Prod.topologicalSpace, induced_inf, induced_compose]
        exact le_reflₓ _,
    continuous_inv_fun :=
      by 
        rw [←continuous_iff_continuous_on_univ, continuous_iff_le_induced]
        simp only [Bundle.TotalSpace.topologicalSpace, induced_inf, induced_compose]
        exact le_reflₓ _,
    BaseSet := univ, open_base_set := is_open_univ, source_eq := rfl,
    target_eq :=
      by 
        simp only [univ_prod_univ],
    proj_to_fun := fun y hy => rfl, linear := fun x hx => ⟨fun y z => rfl, fun c y => rfl⟩ }

-- error in Topology.VectorBundle: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
instance trivial_bundle.topological_vector_bundle : topological_vector_bundle R F (bundle.trivial B F) :=
{ locally_trivial := λ x, ⟨trivial_topological_vector_bundle.trivialization R B F, mem_univ x⟩,
  inducing := λ
  b, ⟨begin
     have [] [":", expr «expr = »(λ x : trivial B F b, x, @id F)] [],
     by { ext [] [ident x] [],
       refl },
     simp [] [] ["only"] ["[", expr total_space.topological_space, ",", expr induced_inf, ",", expr induced_compose, ",", expr function.comp, ",", expr proj, ",", expr induced_const, ",", expr top_inf_eq, ",", expr trivial.proj_snd, ",", expr id.def, ",", expr trivial.topological_space, ",", expr this, ",", expr induced_id, "]"] [] []
   end⟩ }

variable {R B F}

theorem is_topological_vector_bundle_is_topological_fiber_bundle : IsTopologicalFiberBundle F (proj E) :=
  fun x => ⟨(trivialization_at R F E x).toFiberBundleTrivialization, mem_base_set_trivialization_at R F E x⟩

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
  coord_change_self : ∀ i, ∀ x _ : x ∈ base_set i, ∀ v, coord_change i i x v = v 
  coord_change_continuous :
  ∀ i j, ContinuousOn (fun p : B × F => coord_change i j p.1 p.2) (Set.Prod (base_set i ∩ base_set j) univ)
  coord_change_comp :
  ∀ i j k,
    ∀ x _ : x ∈ base_set i ∩ base_set j ∩ base_set k,
      ∀ v, (coord_change j k x) (coord_change i j x v) = coord_change i k x v

attribute [simp, mfld_simps] TopologicalVectorBundleCore.mem_base_set_at

namespace TopologicalVectorBundleCore

variable {R B F} {ι : Type _} (Z : TopologicalVectorBundleCore R B F ι)

/-- Natural identification to a `topological_fiber_bundle_core`. -/
def to_topological_vector_bundle_core : TopologicalFiberBundleCore ι B F :=
  { Z with coordChange := fun i j b => Z.coord_change i j b }

instance to_topological_vector_bundle_core_coe :
  Coe (TopologicalVectorBundleCore R B F ι) (TopologicalFiberBundleCore ι B F) :=
  ⟨to_topological_vector_bundle_core⟩

include Z

theorem coord_change_linear_comp (i j k : ι) :
  ∀ x _ : x ∈ Z.base_set i ∩ Z.base_set j ∩ Z.base_set k,
    (Z.coord_change j k x).comp (Z.coord_change i j x) = Z.coord_change i k x :=
  fun x hx =>
    by 
      ext v 
      exact Z.coord_change_comp i j k x hx v

/-- The index set of a topological vector bundle core, as a convenience function for dot notation -/
@[nolint unused_arguments has_inhabited_instance]
def index :=
  ι

/-- The base space of a topological vector bundle core, as a convenience function for dot notation-/
@[nolint unused_arguments, reducible]
def base :=
  B

/-- The fiber of a topological vector bundle core, as a convenience function for dot notation and
typeclass inference -/
@[nolint unused_arguments has_inhabited_instance]
def fiber (x : B) :=
  F

section FiberInstances

attribute [local reducible] fiber

instance topological_space_fiber (x : B) : TopologicalSpace (Z.fiber x) :=
  by 
    infer_instance

instance add_comm_monoid_fiber : ∀ x : B, AddCommMonoidₓ (Z.fiber x) :=
  fun x =>
    by 
      infer_instance

instance module_fiber : ∀ x : B, Module R (Z.fiber x) :=
  fun x =>
    by 
      infer_instance

end FiberInstances

/-- The projection from the total space of a topological fiber bundle core, on its base. -/
@[reducible, simp, mfld_simps]
def proj : total_space Z.fiber → B :=
  Bundle.proj Z.fiber

/-- Local homeomorphism version of the trivialization change. -/
def triv_change (i j : ι) : LocalHomeomorph (B × F) (B × F) :=
  TopologicalFiberBundleCore.trivChange («expr↑ » Z) i j

@[simp, mfld_simps]
theorem mem_triv_change_source (i j : ι) (p : B × F) :
  p ∈ (Z.triv_change i j).Source ↔ p.1 ∈ Z.base_set i ∩ Z.base_set j :=
  TopologicalFiberBundleCore.mem_triv_change_source («expr↑ » Z) i j p

variable (ι)

/-- Topological structure on the total space of a topological bundle created from core, designed so
that all the local trivialization are continuous. -/
instance to_topological_space : TopologicalSpace (total_space Z.fiber) :=
  TopologicalFiberBundleCore.toTopologicalSpace ι («expr↑ » Z)

variable {ι} (b : B) (a : F)

@[simp, mfld_simps]
theorem coe_cord_change (i j : ι) : TopologicalFiberBundleCore.coordChange («expr↑ » Z) i j b = Z.coord_change i j b :=
  rfl

/-- Extended version of the local trivialization of a fiber bundle constructed from core,
registering additionally in its type that it is a local bundle trivialization. -/
def local_triv (i : ι) : TopologicalVectorBundle.Trivialization R F Z.fiber :=
  { TopologicalFiberBundleCore.localTriv («expr↑ » Z) i with
    linear :=
      fun x hx =>
        { map_add :=
            fun v w =>
              by 
                simp' only [LinearMap.map_add] with mfld_simps,
          map_smul :=
            fun r v =>
              by 
                simp' only [LinearMap.map_smul] with mfld_simps } }

@[simp, mfld_simps]
theorem mem_local_triv_source (i : ι) (p : total_space Z.fiber) : p ∈ (Z.local_triv i).Source ↔ p.1 ∈ Z.base_set i :=
  Iff.rfl

/-- Preferred local trivialization of a vector bundle constructed from core, at a given point, as
a bundle trivialization -/
def local_triv_at (b : B) : TopologicalVectorBundle.Trivialization R F Z.fiber :=
  Z.local_triv (Z.index_at b)

theorem mem_source_at : (⟨b, a⟩ : total_space Z.fiber) ∈ (Z.local_triv_at b).Source :=
  by 
    rw [local_triv_at, mem_local_triv_source]
    exact Z.mem_base_set_at b

@[simp, mfld_simps]
theorem local_triv_at_apply : (Z.local_triv_at b) ⟨b, a⟩ = ⟨b, a⟩ :=
  TopologicalFiberBundleCore.local_triv_at_apply Z b a

instance : TopologicalVectorBundle R F Z.fiber :=
  { Inducing :=
      fun b =>
        ⟨by 
            refine' le_antisymmₓ _ fun s h => _
            ·
              rw [←continuous_iff_le_induced]
              exact TopologicalFiberBundleCore.continuous_total_space_mk («expr↑ » Z) b
            ·
              refine'
                is_open_induced_iff.mpr
                  ⟨(Z.local_triv_at b).Source ∩ Z.local_triv_at b ⁻¹' (Z.local_triv_at b).BaseSet.Prod s,
                    (continuous_on_open_iff (Z.local_triv_at b).open_source).mp (Z.local_triv_at b).continuous_to_fun _
                      (IsOpen.prod (Z.local_triv_at b).open_base_set h),
                    _⟩
              rw [preimage_inter, ←preimage_comp, Function.comp]
              simp only [id.def]
              refine' ext_iff.mpr fun a => ⟨fun ha => _, fun ha => ⟨Z.mem_base_set_at b, _⟩⟩
              ·
                simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply] at ha 
                exact ha.2.2
              ·
                simp only [mem_prod, mem_preimage, mem_inter_eq, local_triv_at_apply]
                exact ⟨Z.mem_base_set_at b, ha⟩⟩,
    locally_trivial := fun b => ⟨Z.local_triv_at b, Z.mem_base_set_at b⟩ }

/-- The projection on the base of a topological vector bundle created from core is continuous -/
@[continuity]
theorem continuous_proj : Continuous Z.proj :=
  TopologicalFiberBundleCore.continuous_proj Z

/-- The projection on the base of a topological vector bundle created from core is an open map -/
theorem is_open_map_proj : IsOpenMap Z.proj :=
  TopologicalFiberBundleCore.is_open_map_proj Z

end TopologicalVectorBundleCore

