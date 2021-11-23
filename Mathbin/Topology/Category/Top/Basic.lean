import Mathbin.CategoryTheory.ConcreteCategory.BundledHom 
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Category instance for topological spaces

We introduce the bundled category `Top` of topological spaces together with the functors `discrete`
and `trivial` from the category of types to `Top` which equip a type with the corresponding
discrete, resp. trivial, topology. For a proof that these functors are left, resp. right adjoint
to the forgetful functor, see `topology.category.Top.adjunctions`.
-/


open CategoryTheory

open TopologicalSpace

universe u

/-- The category of topological spaces and continuous maps. -/
def Top : Type (u + 1) :=
  bundled TopologicalSpace

namespace Top

instance bundled_hom : bundled_hom @ContinuousMap :=
  ⟨@ContinuousMap.toFun, @ContinuousMap.id, @ContinuousMap.comp, @ContinuousMap.coe_inj⟩

-- error in Topology.Category.Top.Basic: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] Top

instance  : CoeSort Top (Type _) :=
  bundled.has_coe_to_sort

instance topological_space_unbundled (x : Top) : TopologicalSpace x :=
  x.str

@[simp]
theorem id_app (X : Top.{u}) (x : X) : (𝟙 X : X → X) x = x :=
  rfl

@[simp]
theorem comp_app {X Y Z : Top.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g : X → Z) x = g (f x) :=
  rfl

/-- Construct a bundled `Top` from the underlying type and the typeclass. -/
def of (X : Type u) [TopologicalSpace X] : Top :=
  ⟨X⟩

instance  (X : Top) : TopologicalSpace X :=
  X.str

@[simp]
theorem coe_of (X : Type u) [TopologicalSpace X] : (of X : Type u) = X :=
  rfl

instance  : Inhabited Top :=
  ⟨Top.of Empty⟩

/-- The discrete topology on any type. -/
def discrete : Type u ⥤ Top.{u} :=
  { obj := fun X => ⟨X, ⊥⟩, map := fun X Y f => { toFun := f, continuous_to_fun := continuous_bot } }

/-- The trivial topology on any type. -/
def trivialₓ : Type u ⥤ Top.{u} :=
  { obj := fun X => ⟨X, ⊤⟩, map := fun X Y f => { toFun := f, continuous_to_fun := continuous_top } }

/-- Any homeomorphisms induces an isomorphism in `Top`. -/
@[simps]
def iso_of_homeo {X Y : Top.{u}} (f : X ≃ₜ Y) : X ≅ Y :=
  { Hom := ⟨f⟩, inv := ⟨f.symm⟩ }

/-- Any isomorphism in `Top` induces a homeomorphism. -/
@[simps]
def homeo_of_iso {X Y : Top.{u}} (f : X ≅ Y) : X ≃ₜ Y :=
  { toFun := f.hom, invFun := f.inv,
    left_inv :=
      fun x =>
        by 
          simp ,
    right_inv :=
      fun x =>
        by 
          simp ,
    continuous_to_fun := f.hom.continuous, continuous_inv_fun := f.inv.continuous }

@[simp]
theorem of_iso_of_homeo {X Y : Top.{u}} (f : X ≃ₜ Y) : homeo_of_iso (iso_of_homeo f) = f :=
  by 
    ext 
    rfl

@[simp]
theorem of_homeo_of_iso {X Y : Top.{u}} (f : X ≅ Y) : iso_of_homeo (homeo_of_iso f) = f :=
  by 
    ext 
    rfl

end Top

