import Mathbin.Algebra.Homology.Homotopy 
import Mathbin.CategoryTheory.Quotient

/-!
# The homotopy category

`homotopy_category V c` gives the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic.
-/


universe v u

open_locale Classical

noncomputable theory

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable{ι : Type _}

variable(V : Type u)[category.{v} V][preadditive V]

variable(c : ComplexShape ι)

/--
The congruence on `homological_complex V c` given by the existence of a homotopy.
-/
def Homotopic : HomRel (HomologicalComplex V c) :=
  fun C D f g => Nonempty (Homotopy f g)

instance homotopy_congruence : congruence (Homotopic V c) :=
  { IsEquiv :=
      fun C D =>
        { refl := fun C => ⟨Homotopy.refl C⟩, symm := fun f g ⟨w⟩ => ⟨w.symm⟩,
          trans := fun f g h ⟨w₁⟩ ⟨w₂⟩ => ⟨w₁.trans w₂⟩ },
    compLeft := fun E F G m₁ m₂ g ⟨i⟩ => ⟨i.comp_left _⟩, compRight := fun E F G f m₁ m₂ ⟨i⟩ => ⟨i.comp_right _⟩ }

-- error in Algebra.Homology.HomotopyCategory: ././Mathport/Syntax/Translate/Basic.lean:704:9: unsupported derive handler category
/-- `homotopy_category V c` is the category of chain complexes of shape `c` in `V`,
with chain maps identified when they are homotopic. -/ @[derive #[expr category]] def homotopy_category :=
category_theory.quotient (homotopic V c)

namespace HomotopyCategory

/-- The quotient functor from complexes to the homotopy category. -/
def Quotientₓ : HomologicalComplex V c ⥤ HomotopyCategory V c :=
  CategoryTheory.Quotient.functor _

attribute [local instance] has_zero_object.has_zero

instance  [has_zero_object V] : Inhabited (HomotopyCategory V c) :=
  ⟨(Quotientₓ V c).obj 0⟩

variable{V c}

@[simp]
theorem quotient_obj_as (C : HomologicalComplex V c) : ((Quotientₓ V c).obj C).as = C :=
  rfl

@[simp]
theorem quotient_map_out {C D : HomotopyCategory V c} (f : C ⟶ D) : (Quotientₓ V c).map f.out = f :=
  Quot.out_eq _

theorem eq_of_homotopy {C D : HomologicalComplex V c} (f g : C ⟶ D) (h : Homotopy f g) :
  (Quotientₓ V c).map f = (Quotientₓ V c).map g :=
  CategoryTheory.Quotient.sound _ ⟨h⟩

/-- If two chain maps become equal in the homotopy category, then they are homotopic. -/
def homotopy_of_eq {C D : HomologicalComplex V c} (f g : C ⟶ D) (w : (Quotientₓ V c).map f = (Quotientₓ V c).map g) :
  Homotopy f g :=
  ((quotient.functor_map_eq_iff _ _ _).mp w).some

/--
An arbitrarily chosen representation of the image of a chain map in the homotopy category
is homotopic to the original chain map.
-/
def homotopy_out_map {C D : HomologicalComplex V c} (f : C ⟶ D) : Homotopy ((Quotientₓ V c).map f).out f :=
  by 
    apply homotopy_of_eq 
    simp 

@[simp]
theorem quotient_map_out_comp_out {C D E : HomotopyCategory V c} (f : C ⟶ D) (g : D ⟶ E) :
  (Quotientₓ V c).map (Quot.out f ≫ Quot.out g) = f ≫ g :=
  by 
    convRHS => erw [←quotient_map_out f, ←quotient_map_out g, ←(Quotientₓ V c).map_comp]

/-- Homotopy equivalent complexes become isomorphic in the homotopy category. -/
@[simps]
def iso_of_homotopy_equiv {C D : HomologicalComplex V c} (f : HomotopyEquiv C D) :
  (Quotientₓ V c).obj C ≅ (Quotientₓ V c).obj D :=
  { Hom := (Quotientₓ V c).map f.hom, inv := (Quotientₓ V c).map f.inv,
    hom_inv_id' :=
      by 
        rw [←(Quotientₓ V c).map_comp, ←(Quotientₓ V c).map_id]
        exact eq_of_homotopy _ _ f.homotopy_hom_inv_id,
    inv_hom_id' :=
      by 
        rw [←(Quotientₓ V c).map_comp, ←(Quotientₓ V c).map_id]
        exact eq_of_homotopy _ _ f.homotopy_inv_hom_id }

/-- If two complexes become isomorphic in the homotopy category,
  then they were homotopy equivalent. -/
def homotopy_equiv_of_iso {C D : HomologicalComplex V c} (i : (Quotientₓ V c).obj C ≅ (Quotientₓ V c).obj D) :
  HomotopyEquiv C D :=
  { Hom := Quot.out i.hom, inv := Quot.out i.inv,
    homotopyHomInvId :=
      homotopy_of_eq _ _
        (by 
          simp 
          rfl),
    homotopyInvHomId :=
      homotopy_of_eq _ _
        (by 
          simp 
          rfl) }

variable(V c)[has_zero_object V][has_equalizers V][has_images V][has_image_maps V][has_cokernels V]

/-- The `i`-th homology, as a functor from the homotopy category. -/
def homologyFunctor (i : ι) : HomotopyCategory V c ⥤ V :=
  CategoryTheory.Quotient.lift _ (homologyFunctor V c i) fun C D f g ⟨h⟩ => homology_map_eq_of_homotopy h i

/-- The homology functor on the homotopy category is just the usual homology functor. -/
def homology_factors (i : ι) : Quotientₓ V c ⋙ homologyFunctor V c i ≅ _root_.homology_functor V c i :=
  CategoryTheory.Quotient.lift.isLift _ _ _

@[simp]
theorem homology_factors_hom_app (i : ι) (C : HomologicalComplex V c) : (homology_factors V c i).Hom.app C = 𝟙 _ :=
  rfl

@[simp]
theorem homology_factors_inv_app (i : ι) (C : HomologicalComplex V c) : (homology_factors V c i).inv.app C = 𝟙 _ :=
  rfl

theorem homology_functor_map_factors (i : ι) {C D : HomologicalComplex V c} (f : C ⟶ D) :
  (_root_.homology_functor V c i).map f = ((homologyFunctor V c i).map ((Quotientₓ V c).map f) : _) :=
  (CategoryTheory.Quotient.lift_map_functor_map _ (_root_.homology_functor V c i) _ f).symm

end HomotopyCategory

namespace CategoryTheory

variable{V}{W : Type _}[category W][preadditive W]

/-- An additive functor induces a functor between homotopy categories. -/
@[simps]
def functor.map_homotopy_category (c : ComplexShape ι) (F : V ⥤ W) [F.additive] :
  HomotopyCategory V c ⥤ HomotopyCategory W c :=
  { obj := fun C => (HomotopyCategory.quotient W c).obj ((F.map_homological_complex c).obj C.as),
    map := fun C D f => (HomotopyCategory.quotient W c).map ((F.map_homological_complex c).map (Quot.out f)),
    map_id' :=
      fun C =>
        by 
          rw [←(HomotopyCategory.quotient W c).map_id]
          apply HomotopyCategory.eq_of_homotopy 
          rw [←(F.map_homological_complex c).map_id]
          apply F.map_homotopy 
          apply HomotopyCategory.homotopyOfEq 
          exact Quot.out_eq _,
    map_comp' :=
      fun C D E f g =>
        by 
          rw [←(HomotopyCategory.quotient W c).map_comp]
          apply HomotopyCategory.eq_of_homotopy 
          rw [←(F.map_homological_complex c).map_comp]
          apply F.map_homotopy 
          apply HomotopyCategory.homotopyOfEq 
          convert Quot.out_eq _ 
          exact HomotopyCategory.quotient_map_out_comp_out _ _ }

/-- A natural transformation induces a natural transformation between
  the induced functors on the homotopy category. -/
@[simps]
def nat_trans.map_homotopy_category {F G : V ⥤ W} [F.additive] [G.additive] (α : F ⟶ G) (c : ComplexShape ι) :
  F.map_homotopy_category c ⟶ G.map_homotopy_category c :=
  { app := fun C => (HomotopyCategory.quotient W c).map ((nat_trans.map_homological_complex α c).app C.as),
    naturality' :=
      fun C D f =>
        by 
          dsimp 
          simp only [←functor.map_comp]
          congr 1 
          ext 
          dsimp 
          simp  }

@[simp]
theorem nat_trans.map_homotopy_category_id (c : ComplexShape ι) (F : V ⥤ W) [F.additive] :
  nat_trans.map_homotopy_category (𝟙 F) c = 𝟙 (F.map_homotopy_category c) :=
  by 
    tidy

@[simp]
theorem nat_trans.map_homotopy_category_comp (c : ComplexShape ι) {F G H : V ⥤ W} [F.additive] [G.additive] [H.additive]
  (α : F ⟶ G) (β : G ⟶ H) :
  nat_trans.map_homotopy_category (α ≫ β) c =
    nat_trans.map_homotopy_category α c ≫ nat_trans.map_homotopy_category β c :=
  by 
    tidy

end CategoryTheory

