import Mathbin.CategoryTheory.Shift

/-!
# Differential objects in a category.

A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.

We build the category of differential objects, and some basic constructions
such as the forgetful functor, zero morphisms and zero objects, and the shift functor
on differential objects.
-/


open CategoryTheory.Limits

universe v u

namespace CategoryTheory

variable (C : Type u) [category.{v} C]

variable [has_zero_morphisms C] [has_shift C]

/-- 
A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure differential_object where
  x : C
  d : X ⟶ X⟦1⟧
  d_squared' : d ≫ d⟦1⟧' = 0 := by
    run_tac
      obviously

restate_axiom differential_object.d_squared'

attribute [simp] differential_object.d_squared

variable {C}

namespace DifferentialObject

/-- 
A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure hom (X Y : differential_object C) where
  f : X.X ⟶ Y.X
  comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d := by
    run_tac
      obviously

restate_axiom hom.comm'

attribute [simp, reassoc] hom.comm

namespace Hom

/--  The identity morphism of a differential object. -/
@[simps]
def id (X : differential_object C) : hom X X :=
  { f := 𝟙 X.X }

/--  The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : differential_object C} (f : hom X Y) (g : hom Y Z) : hom X Z :=
  { f := f.f ≫ g.f }

end Hom

-- failed to format: format: uncaught backtrack exception
instance
  category_of_differential_objects
  : category ( differential_object C )
  where Hom := hom id := hom.id comp X Y Z f g := hom.comp f g

@[simp]
theorem id_f (X : differential_object C) : (𝟙 X : X ⟶ X).f = 𝟙 X.X :=
  rfl

@[simp]
theorem comp_f {X Y Z : differential_object C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

variable (C)

/--  The forgetful functor taking a differential object to its underlying object. -/
def forget : differential_object C ⥤ C :=
  { obj := fun X => X.X, map := fun X Y f => f.f }

instance forget_faithful : faithful (forget C) :=
  {  }

-- failed to format: format: uncaught backtrack exception
instance has_zero_morphisms : has_zero_morphisms ( differential_object C ) where HasZero X Y := ⟨ { f := 0 } ⟩

variable {C}

@[simp]
theorem zero_f (P Q : differential_object C) : (0 : P ⟶ Q).f = 0 :=
  rfl

/-- 
An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps]
def iso_app {X Y : differential_object C} (f : X ≅ Y) : X.X ≅ Y.X :=
  ⟨f.hom.f, f.inv.f, by
    dsimp
    rw [← comp_f, iso.hom_inv_id, id_f], by
    dsimp
    rw [← comp_f, iso.inv_hom_id, id_f]⟩

@[simp]
theorem iso_app_refl (X : differential_object C) : iso_app (iso.refl X) = iso.refl X.X :=
  rfl

@[simp]
theorem iso_app_symm {X Y : differential_object C} (f : X ≅ Y) : iso_app f.symm = (iso_app f).symm :=
  rfl

@[simp]
theorem iso_app_trans {X Y Z : differential_object C} (f : X ≅ Y) (g : Y ≅ Z) :
    iso_app (f ≪≫ g) = iso_app f ≪≫ iso_app g :=
  rfl

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [category.{v'} D]

variable [has_zero_morphisms D] [has_shift D]

/-- 
A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def map_differential_object (F : C ⥤ D) (η : (shift C).Functor.comp F ⟶ F.comp (shift D).Functor)
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : differential_object C ⥤ differential_object D :=
  { obj := fun X =>
      { x := F.obj X.X, d := F.map X.d ≫ η.app X.X,
        d_squared' := by
          dsimp
          rw [functor.map_comp, ← functor.comp_map F (shift D).Functor]
          slice_lhs 2 3 => rw [← η.naturality X.d]
          rw [functor.comp_map]
          slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
          rw [zero_comp, zero_comp] },
    map := fun X Y f =>
      { f := F.map f.f,
        comm' := by
          dsimp
          slice_lhs 2 3 => rw [← functor.comp_map F (shift D).Functor, ← η.naturality f.f]
          slice_lhs 1 2 => rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
          rw [category.assoc] },
    map_id' := by
      intros
      ext
      simp ,
    map_comp' := by
      intros
      ext
      simp }

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (C : Type u) [category.{v} C]

variable [has_zero_object C] [has_zero_morphisms C] [has_shift C]

open_locale ZeroObject

-- failed to format: format: uncaught backtrack exception
instance
  has_zero_object
  : has_zero_object ( differential_object C )
  where
    zero := { x := ( 0 : C ) , d := 0 }
      uniqueTo X := ⟨ ⟨ { f := 0 } ⟩ , fun f => by ext ⟩
      uniqueFrom X := ⟨ ⟨ { f := 0 } ⟩ , fun f => by ext ⟩

end DifferentialObject

namespace DifferentialObject

variable (C : Type (u + 1)) [large_category C] [concrete_category C] [has_zero_morphisms C] [has_shift C]

instance concrete_category_of_differential_objects : concrete_category (differential_object C) where
  forget := forget C ⋙ CategoryTheory.forget C

instance : has_forget₂ (differential_object C) C where
  forget₂ := forget C

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable (C : Type u) [category.{v} C]

variable [has_zero_morphisms C] [has_shift C]

/--  The shift functor on `differential_object C`. -/
@[simps]
def shift_functor : differential_object C ⥤ differential_object C :=
  { obj := fun X =>
      { x := X.X⟦1⟧, d := X.d⟦1⟧',
        d_squared' := by
          dsimp
          rw [← functor.map_comp, X.d_squared, is_equivalence_preserves_zero_morphisms] },
    map := fun X Y f =>
      { f := f.f⟦1⟧',
        comm' := by
          dsimp
          rw [← functor.map_comp, f.comm, ← functor.map_comp] } }

/--  The inverse shift functor on `differential C`, at the level of objects. -/
@[simps]
def shift_inverse_obj : differential_object C → differential_object C := fun X =>
  { x := X.X⟦-1⟧, d := X.d⟦-1⟧' ≫ (shift C).unitInv.app X.X ≫ (shift C).counitInv.app X.X,
    d_squared' := by
      dsimp
      rw [functor.map_comp]
      slice_lhs 3 4 => erw [← (shift C).counitInv.naturality]
      slice_lhs 2 3 => erw [← (shift C).unitInv.naturality]
      slice_lhs 1 2 => erw [← functor.map_comp, X.d_squared]
      simp }

/--  The inverse shift functor on `differential C`. -/
@[simps]
def shift_inverse : differential_object C ⥤ differential_object C :=
  { obj := shift_inverse_obj C,
    map := fun X Y f =>
      { f := f.f⟦-1⟧',
        comm' := by
          dsimp
          slice_lhs 3 4 => erw [← (shift C).counitInv.naturality]
          slice_lhs 2 3 => erw [← (shift C).unitInv.naturality]
          slice_lhs 1 2 => erw [← functor.map_comp, f.comm, functor.map_comp]
          rw [category.assoc, category.assoc] } }

/--  The unit for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit : 𝟭 (differential_object C) ⟶ shift_functor C ⋙ shift_inverse C :=
  { app := fun X =>
      { f := (shift C).Unit.app X.X,
        comm' := by
          dsimp
          slice_rhs 1 2 => erw [← (shift C).Unit.naturality]
          simp only [category.comp_id, functor.id_map, iso.hom_inv_id_app, category.assoc,
            equivalence.counit_inv_app_functor] } }

/--  The inverse of the unit for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit_inv : shift_functor C ⋙ shift_inverse C ⟶ 𝟭 (differential_object C) :=
  { app := fun X =>
      { f := (shift C).unitInv.app X.X,
        comm' := by
          dsimp
          slice_rhs 1 2 => erw [← (shift C).unitInv.naturality]
          rw [equivalence.counit_inv_app_functor]
          slice_lhs 3 4 => rw [← functor.map_comp]
          simp only [iso.hom_inv_id_app, functor.comp_map, iso.hom_inv_id_app_assoc, nat_iso.cancel_nat_iso_inv_left,
            equivalence.inv_fun_map, category.assoc]
          dsimp
          rw [CategoryTheory.Functor.map_id] } }

/--  The unit isomorphism for the shift functor on `differential_object C`. -/
@[simps]
def shift_unit_iso : 𝟭 (differential_object C) ≅ shift_functor C ⋙ shift_inverse C :=
  { Hom := shift_unit C, inv := shift_unit_inv C }

/--  The counit for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit : shift_inverse C ⋙ shift_functor C ⟶ 𝟭 (differential_object C) :=
  { app := fun X =>
      { f := (shift C).counit.app X.X,
        comm' := by
          dsimp
          slice_rhs 1 2 => erw [← (shift C).counit.naturality]
          rw [(shift C).Functor.map_comp, (shift C).Functor.map_comp]
          slice_lhs 3 4 => erw [← functor.map_comp, iso.inv_hom_id_app, Functor.map_id]
          erw [equivalence.counit_app_functor]
          rw [category.comp_id]
          rfl } }

/--  The inverse of the counit for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit_inv : 𝟭 (differential_object C) ⟶ shift_inverse C ⋙ shift_functor C :=
  { app := fun X =>
      { f := (shift C).counitInv.app X.X,
        comm' := by
          dsimp
          rw [(shift C).Functor.map_comp, (shift C).Functor.map_comp]
          slice_rhs 1 2 => erw [← (shift C).counitInv.naturality]
          rw [← equivalence.counit_app_functor]
          slice_rhs 2 3 => rw [iso.inv_hom_id_app]
          rw [category.id_comp]
          rfl } }

/--  The counit isomorphism for the shift functor on `differential_object C`. -/
@[simps]
def shift_counit_iso : shift_inverse C ⋙ shift_functor C ≅ 𝟭 (differential_object C) :=
  { Hom := shift_counit C, inv := shift_counit_inv C }

/-- 
The category of differential objects in `C` itself has a shift functor.
-/
instance : has_shift (differential_object C) where
  shift :=
    { Functor := shift_functor C, inverse := shift_inverse C, unitIso := shift_unit_iso C,
      counitIso := shift_counit_iso C }

end DifferentialObject

end CategoryTheory

