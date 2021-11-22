import Mathbin.CategoryTheory.Monad.Limits 
import Mathbin.Topology.UniformSpace.Completion 
import Mathbin.Topology.Category.Top.Basic

/-!
# The category of uniform spaces

We construct the category of uniform spaces, show that the complete separated uniform spaces
form a reflective subcategory, and hence possess all limits that uniform spaces do.

TODO: show that uniform spaces actually have all limits!
-/


universe u

open CategoryTheory

/-- A (bundled) uniform space. -/
def UniformSpaceₓ : Type (u + 1) :=
  bundled UniformSpace

namespace UniformSpaceₓ

/-- The information required to build morphisms for `UniformSpace`. -/
instance  : unbundled_hom @UniformContinuous :=
  ⟨@uniform_continuous_id, @UniformContinuous.comp⟩

-- error in Topology.Category.UniformSpace: ././Mathport/Syntax/Translate/Basic.lean:702:9: unsupported derive handler large_category
attribute [derive #["[", expr large_category, ",", expr concrete_category, "]"]] UniformSpace

instance  : CoeSort UniformSpaceₓ (Type _) :=
  bundled.has_coe_to_sort

instance  (x : UniformSpaceₓ) : UniformSpace x :=
  x.str

/-- Construct a bundled `UniformSpace` from the underlying type and the typeclass. -/
def of (α : Type u) [UniformSpace α] : UniformSpaceₓ :=
  ⟨α⟩

instance  : Inhabited UniformSpaceₓ :=
  ⟨UniformSpaceₓ.of Empty⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] : (of X : Type u) = X :=
  rfl

instance  (X Y : UniformSpaceₓ) : CoeFun (X ⟶ Y) fun _ => X → Y :=
  ⟨CategoryTheory.Functor.map (forget UniformSpaceₓ)⟩

@[simp]
theorem coe_comp {X Y Z : UniformSpaceₓ} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g : X → Z) = (g ∘ f) :=
  rfl

@[simp]
theorem coe_id (X : UniformSpaceₓ) : (𝟙 X : X → X) = id :=
  rfl

@[simp]
theorem coe_mk {X Y : UniformSpaceₓ} (f : X → Y) (hf : UniformContinuous f) : ((⟨f, hf⟩ : X ⟶ Y) : X → Y) = f :=
  rfl

theorem hom_ext {X Y : UniformSpaceₓ} {f g : X ⟶ Y} : (f : X → Y) = g → f = g :=
  Subtype.eq

/-- The forgetful functor from uniform spaces to topological spaces. -/
instance has_forget_to_Top : has_forget₂ UniformSpaceₓ.{u} Top.{u} :=
  { forget₂ :=
      { obj := fun X => Top.of X,
        map := fun X Y f => { toFun := f, continuous_to_fun := UniformContinuous.continuous f.property } } }

end UniformSpaceₓ

/-- A (bundled) complete separated uniform space. -/
structure CpltSepUniformSpace where 
  α : Type u
  [isUniformSpace : UniformSpace α]
  [is_complete_space : CompleteSpace α]
  [IsSeparated : SeparatedSpace α]

namespace CpltSepUniformSpace

instance  : CoeSort CpltSepUniformSpace (Type u) :=
  ⟨CpltSepUniformSpace.α⟩

attribute [instance] is_uniform_space is_complete_space IsSeparated

/-- The function forgetting that a complete separated uniform spaces is complete and separated. -/
def to_UniformSpace (X : CpltSepUniformSpace) : UniformSpaceₓ :=
  UniformSpaceₓ.of X

instance CompleteSpace (X : CpltSepUniformSpace) : CompleteSpace (to_UniformSpace X).α :=
  CpltSepUniformSpace.is_complete_space X

instance SeparatedSpace (X : CpltSepUniformSpace) : SeparatedSpace (to_UniformSpace X).α :=
  CpltSepUniformSpace.is_separated X

/-- Construct a bundled `UniformSpace` from the underlying type and the appropriate typeclasses. -/
def of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : CpltSepUniformSpace :=
  ⟨X⟩

@[simp]
theorem coe_of (X : Type u) [UniformSpace X] [CompleteSpace X] [SeparatedSpace X] : (of X : Type u) = X :=
  rfl

instance  : Inhabited CpltSepUniformSpace :=
  by 
    haveI  : SeparatedSpace Empty :=
      separated_iff_t2.mpr
        (by 
          infer_instance)
    exact ⟨CpltSepUniformSpace.of Empty⟩

/-- The category instance on `CpltSepUniformSpace`. -/
instance category : large_category CpltSepUniformSpace :=
  induced_category.category to_UniformSpace

/-- The concrete category instance on `CpltSepUniformSpace`. -/
instance concrete_category : concrete_category CpltSepUniformSpace :=
  induced_category.concrete_category to_UniformSpace

instance has_forget_to_UniformSpace : has_forget₂ CpltSepUniformSpace UniformSpaceₓ :=
  induced_category.has_forget₂ to_UniformSpace

end CpltSepUniformSpace

namespace UniformSpaceₓ

open UniformSpace

open CpltSepUniformSpace

/-- The functor turning uniform spaces into complete separated uniform spaces. -/
noncomputable def completion_functor : UniformSpaceₓ ⥤ CpltSepUniformSpace :=
  { obj := fun X => CpltSepUniformSpace.of (completion X),
    map := fun X Y f => ⟨completion.map f.1, completion.uniform_continuous_map⟩,
    map_id' := fun X => Subtype.eq completion.map_id,
    map_comp' := fun X Y Z f g => Subtype.eq (completion.map_comp g.property f.property).symm }

/-- The inclusion of a uniform space into its completion. -/
def completion_hom (X : UniformSpaceₓ) :
  X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceₓ).obj (completion_functor.obj X) :=
  { val := (coeₓ : X → completion X), property := completion.uniform_continuous_coe X }

@[simp]
theorem completion_hom_val (X : UniformSpaceₓ) x : (completion_hom X) x = (x : completion X) :=
  rfl

/-- The mate of a morphism from a `UniformSpace` to a `CpltSepUniformSpace`. -/
noncomputable def extension_hom {X : UniformSpaceₓ} {Y : CpltSepUniformSpace}
  (f : X ⟶ (forget₂ CpltSepUniformSpace UniformSpaceₓ).obj Y) : completion_functor.obj X ⟶ Y :=
  { val := completion.extension f, property := completion.uniform_continuous_extension }

@[simp]
theorem extension_hom_val {X : UniformSpaceₓ} {Y : CpltSepUniformSpace} (f : X ⟶ (forget₂ _ _).obj Y) x :
  (extension_hom f) x = completion.extension f x :=
  rfl

@[simp]
theorem extension_comp_coe {X : UniformSpaceₓ} {Y : CpltSepUniformSpace}
  (f : to_UniformSpace (CpltSepUniformSpace.of (completion X)) ⟶ to_UniformSpace Y) :
  extension_hom (completion_hom X ≫ f) = f :=
  by 
    apply Subtype.eq 
    funext x 
    exact congr_funₓ (completion.extension_comp_coe f.property) x

/-- The completion functor is left adjoint to the forgetful functor. -/
noncomputable def adj : completion_functor ⊣ forget₂ CpltSepUniformSpace UniformSpaceₓ :=
  adjunction.mk_of_hom_equiv
    { homEquiv :=
        fun X Y =>
          { toFun := fun f => completion_hom X ≫ f, invFun := fun f => extension_hom f,
            left_inv :=
              fun f =>
                by 
                  dsimp 
                  erw [extension_comp_coe],
            right_inv :=
              fun f =>
                by 
                  apply Subtype.eq 
                  funext x 
                  cases f 
                  exact @completion.extension_coe _ _ _ _ _ (CpltSepUniformSpace.separated_space _) f_property _ },
      hom_equiv_naturality_left_symm' :=
        fun X X' Y f g =>
          by 
            apply hom_ext 
            funext x 
            dsimp 
            erw [coe_comp, ←completion.extension_map]
            rfl 
            exact g.property 
            exact f.property }

noncomputable instance  : is_right_adjoint (forget₂ CpltSepUniformSpace UniformSpaceₓ) :=
  ⟨completion_functor, adj⟩

noncomputable instance  : reflective (forget₂ CpltSepUniformSpace UniformSpaceₓ) :=
  {  }

open CategoryTheory.Limits

example  [has_limits.{u} UniformSpaceₓ.{u}] : has_limits.{u} CpltSepUniformSpace.{u} :=
  has_limits_of_reflective$ forget₂ CpltSepUniformSpace UniformSpaceₓ.{u}

end UniformSpaceₓ

