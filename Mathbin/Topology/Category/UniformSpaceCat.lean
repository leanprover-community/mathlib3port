/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Patrick Massot, Scott Morrison
-/
import Mathbin.CategoryTheory.Adjunction.Reflective
import Mathbin.CategoryTheory.ConcreteCategory.UnbundledHom
import Mathbin.CategoryTheory.Monad.Limits
import Mathbin.CategoryTheory.Limits.HasLimits
import Mathbin.Topology.Category.TopCat.Basic
import Mathbin.Topology.UniformSpace.Completion

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/


universe u

open CategoryTheory

/-- A (bundled) uniform space. -/
def UniformSpaceCat : Type (u + 1) :=
  Bundled UniformSpace

namespace UniformSpaceCat

/-- The information required to build morphisms for `UniformSpace`. -/
instance : UnbundledHom @UniformContinuous :=
  ⟨@uniform_continuous_id, @UniformContinuous.comp⟩

deriving instance LargeCategory, ConcreteCategory for UniformSpaceCat

instance : CoeSort UniformSpaceCat (Type _) :=
  bundled.has_coe_to_sort

instance (x : UniformSpaceCat) : UniformSpace x :=
  x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [UniformSpace α] : UniformSpaceCat :=
  ⟨α⟩

instance : Inhabited UniformSpaceCat :=
  ⟨UniformSpaceCat.of Empty⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

instance (X Y : UniformSpaceCat) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨CategoryTheory.Functor.map (forget UniformSpaceCat)⟩

@[simp]
theorem coe_comp {X Y Z : UniformSpaceCat} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = g ∘ f :=
  rfl

@[simp]
theorem coe_id (X : UniformSpaceCat) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_mk {X Y : UniformSpaceCat} (f : X → Y) (hf : UniformContinuous f) : ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f :=
  rfl

theorem hom_ext {X Y : UniformSpaceCat} {f g : X ⟶ Y} : (f : X → Y) = g → f = g :=
  Subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance hasForgetToTop :
    HasForget₂ UniformSpaceCat.{u}
      TopCat.{u} where forget₂ :=
    { obj := fun X => TopCat.of X,
      map := fun X Y f => { toFun := f, continuous_to_fun := UniformContinuous.continuous f.property } }

end UniformSpaceCat

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpaceCat where
  α : Type u
  [isUniformSpace : UniformSpace α]
  [is_complete_space : CompleteSpace α]
  [is_separated : SeparatedSpace α]

namespace CpltSepUniformSpaceCat

instance : CoeSort CpltSepUniformSpaceCat (Type u) :=
  ⟨CpltSepUniformSpaceCat.α⟩

attribute [instance] is_uniform_space is_complete_space is_separated

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def toUniformSpace (X : CpltSepUniformSpaceCat) : UniformSpaceCat :=
  UniformSpaceCat.of X

instance complete_space (X : CpltSepUniformSpaceCat) : CompleteSpace (toUniformSpace X).α :=
  CpltSepUniformSpaceCat.is_complete_space X

instance separated_space (X : CpltSepUniformSpaceCat) : SeparatedSpace (toUniformSpace X).α :=
  CpltSepUniformSpaceCat.is_separated X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : CpltSepUniformSpaceCat :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : (of X : Type u) = X :=
  rfl

instance : Inhabited CpltSepUniformSpaceCat :=
  haveI : SeparatedSpace Empty := separated_iff_t2.mpr (by infer_instance)
  ⟨CpltSepUniformSpaceCat.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : LargeCategory CpltSepUniformSpaceCat :=
  InducedCategory.category toUniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concreteCategory : ConcreteCategory CpltSepUniformSpaceCat :=
  InducedCategory.concreteCategory toUniformSpace

instance hasForgetToUniformSpace : HasForget₂ CpltSepUniformSpaceCat UniformSpaceCat :=
  InducedCategory.hasForget₂ toUniformSpace

end CpltSepUniformSpaceCat

namespace UniformSpaceCat

open UniformSpace

open CpltSepUniformSpaceCat

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completionFunctor : UniformSpaceCat ⥤ CpltSepUniformSpaceCat where
  obj X := CpltSepUniformSpaceCat.of (Completion X)
  map X Y f := ⟨Completion.map f.1, Completion.uniform_continuous_map⟩
  map_id' X := Subtype.eq Completion.map_id
  map_comp' X Y Z f g := Subtype.eq (Completion.map_comp g.property f.property).symm

/-- The inclusion of a uniform space into its completion. -/
def completionHom (X : UniformSpaceCat) :
    X ⟶ (forget₂ CpltSepUniformSpaceCat UniformSpaceCat).obj (completionFunctor.obj X) where
  val := (coe : X → Completion X)
  property := Completion.uniform_continuous_coe X

@[simp]
theorem completion_hom_val (X : UniformSpaceCat) (x) : (completionHom X) x = (x : Completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extensionHom {X : UniformSpaceCat} {Y : CpltSepUniformSpaceCat}
    (f : X ⟶ (forget₂ CpltSepUniformSpaceCat UniformSpaceCat).obj Y) : completionFunctor.obj X ⟶ Y where
  val := Completion.extension f
  property := Completion.uniform_continuous_extension

@[simp]
theorem extension_hom_val {X : UniformSpaceCat} {Y : CpltSepUniformSpaceCat} (f : X ⟶ (forget₂ _ _).obj Y) (x) :
    (extensionHom f) x = Completion.extension f x :=
  rfl

@[simp]
theorem extension_comp_coe {X : UniformSpaceCat} {Y : CpltSepUniformSpaceCat}
    (f : toUniformSpace (CpltSepUniformSpaceCat.of (Completion X)) ⟶ toUniformSpace Y) :
    extensionHom (completionHom X ≫ f) = f := by
  apply Subtype.eq
  funext x
  exact congr_fun (completion.extension_comp_coe f.property) x

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completion_functor ⊣ forget₂ CpltSepUniformSpaceCat UniformSpaceCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => completionHom X ≫ f, invFun := fun f => extensionHom f,
          left_inv := fun f => by
            dsimp
            erw [extension_comp_coe],
          right_inv := fun f => by
            apply Subtype.eq
            funext x
            cases f
            exact @completion.extension_coe _ _ _ _ _ (CpltSepUniformSpaceCat.separated_space _) f_property _ },
      hom_equiv_naturality_left_symm' := fun X X' Y f g => by
        apply hom_ext
        funext x
        dsimp
        erw [coe_comp, ← completion.extension_map]
        rfl
        exact g.property
        exact f.property }

noncomputable instance : IsRightAdjoint (forget₂ CpltSepUniformSpaceCat UniformSpaceCat) :=
  ⟨completionFunctor, adj⟩

noncomputable instance : Reflective (forget₂ CpltSepUniformSpaceCat UniformSpaceCat) where

open CategoryTheory.Limits

-- TODO Once someone defines `has_limits UniformSpace`, turn this into an instance.
example [HasLimits.{u} UniformSpaceCat.{u}] : HasLimits.{u} CpltSepUniformSpaceCat.{u} :=
  has_limits_of_reflective <| forget₂ CpltSepUniformSpaceCat UniformSpaceCat.{u}

end UniformSpaceCat

