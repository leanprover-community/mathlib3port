/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
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

variable (C : Type u) [Category.{v} C]

-- TODO: generaize to `has_shift C A` for an arbitrary `[add_monoid A]` `[has_one A]`.
variable [HasZeroMorphisms C] [HasShift C ℤ]

/-- A differential object in a category with zero morphisms and a shift is
an object `X` equipped with
a morphism `d : X ⟶ X⟦1⟧`, such that `d^2 = 0`.
-/
@[nolint has_inhabited_instance]
structure DifferentialObject where
  x : C
  d : X ⟶ X⟦1⟧
  d_squared' : d ≫ d⟦(1 : ℤ)⟧' = 0 := by
    run_tac
      obviously

restate_axiom differential_object.d_squared'

attribute [simp] differential_object.d_squared

variable {C}

namespace DifferentialObject

/-- A morphism of differential objects is a morphism commuting with the differentials.
-/
@[ext, nolint has_inhabited_instance]
structure Hom (X Y : DifferentialObject C) where
  f : X.x ⟶ Y.x
  comm' : X.d ≫ f⟦1⟧' = f ≫ Y.d := by
    run_tac
      obviously

restate_axiom hom.comm'

attribute [simp, reassoc] hom.comm

namespace Hom

/-- The identity morphism of a differential object. -/
@[simps]
def id (X : DifferentialObject C) : Hom X X where
  f := 𝟙 X.x

/-- The composition of morphisms of differential objects. -/
@[simps]
def comp {X Y Z : DifferentialObject C} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  f := f.f ≫ g.f

end Hom

instance categoryOfDifferentialObjects : Category (DifferentialObject C) where
  Hom := Hom
  id := Hom.id
  comp := fun X Y Z f g => Hom.comp f g

@[simp]
theorem id_f (X : DifferentialObject C) : (𝟙 X : X ⟶ X).f = 𝟙 X.x :=
  rfl

@[simp]
theorem comp_f {X Y Z : DifferentialObject C} (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).f = f.f ≫ g.f :=
  rfl

@[simp]
theorem eq_to_hom_f {X Y : DifferentialObject C} (h : X = Y) : Hom.f (eqToHom h) = eqToHom (congr_argₓ _ h) := by
  subst h
  rw [eq_to_hom_refl, eq_to_hom_refl]
  rfl

variable (C)

/-- The forgetful functor taking a differential object to its underlying object. -/
def forget : DifferentialObject C ⥤ C where
  obj := fun X => X.x
  map := fun X Y f => f.f

instance forget_faithful : Faithful (forget C) :=
  {  }

instance hasZeroMorphisms : HasZeroMorphisms (DifferentialObject C) where
  HasZero := fun X Y => ⟨{ f := 0 }⟩

variable {C}

@[simp]
theorem zero_f (P Q : DifferentialObject C) : (0 : P ⟶ Q).f = 0 :=
  rfl

/-- An isomorphism of differential objects gives an isomorphism of the underlying objects.
-/
@[simps]
def isoApp {X Y : DifferentialObject C} (f : X ≅ Y) : X.x ≅ Y.x :=
  ⟨f.Hom.f, f.inv.f, by
    dsimp
    rw [← comp_f, iso.hom_inv_id, id_f], by
    dsimp
    rw [← comp_f, iso.inv_hom_id, id_f]⟩

@[simp]
theorem iso_app_refl (X : DifferentialObject C) : isoApp (Iso.refl X) = Iso.refl X.x :=
  rfl

@[simp]
theorem iso_app_symm {X Y : DifferentialObject C} (f : X ≅ Y) : isoApp f.symm = (isoApp f).symm :=
  rfl

@[simp]
theorem iso_app_trans {X Y Z : DifferentialObject C} (f : X ≅ Y) (g : Y ≅ Z) : isoApp (f ≪≫ g) = isoApp f ≪≫ isoApp g :=
  rfl

/-- An isomorphism of differential objects can be constructed
from an isomorphism of the underlying objects that commutes with the differentials. -/
@[simps]
def mkIso {X Y : DifferentialObject C} (f : X.x ≅ Y.x) (hf : X.d ≫ f.Hom⟦1⟧' = f.Hom ≫ Y.d) : X ≅ Y where
  Hom := ⟨f.Hom, hf⟩
  inv :=
    ⟨f.inv, by
      dsimp
      rw [← functor.map_iso_inv, iso.comp_inv_eq, category.assoc, iso.eq_inv_comp, functor.map_iso_hom, hf]⟩
  hom_inv_id' := by
    ext1
    dsimp
    exact f.hom_inv_id
  inv_hom_id' := by
    ext1
    dsimp
    exact f.inv_hom_id

end DifferentialObject

namespace Functor

universe v' u'

variable (D : Type u') [Category.{v'} D]

variable [HasZeroMorphisms D] [HasShift D ℤ]

/-- A functor `F : C ⥤ D` which commutes with shift functors on `C` and `D` and preserves zero morphisms
can be lifted to a functor `differential_object C ⥤ differential_object D`.
-/
@[simps]
def mapDifferentialObject (F : C ⥤ D) (η : (shiftFunctor C (1 : ℤ)).comp F ⟶ F.comp (shiftFunctor D (1 : ℤ)))
    (hF : ∀ c c', F.map (0 : c ⟶ c') = 0) : DifferentialObject C ⥤ DifferentialObject D where
  obj := fun X =>
    { x := F.obj X.x, d := F.map X.d ≫ η.app X.x,
      d_squared' := by
        rw [functor.map_comp, ← functor.comp_map F (shift_functor D (1 : ℤ))]
        slice_lhs 2 3 => rw [← η.naturality X.d]
        rw [functor.comp_map]
        slice_lhs 1 2 => rw [← F.map_comp, X.d_squared, hF]
        rw [zero_comp, zero_comp] }
  map := fun X Y f =>
    { f := F.map f.f,
      comm' := by
        dsimp
        slice_lhs 2 3 => rw [← functor.comp_map F (shift_functor D (1 : ℤ)), ← η.naturality f.f]
        slice_lhs 1 2 => rw [functor.comp_map, ← F.map_comp, f.comm, F.map_comp]
        rw [category.assoc] }
  map_id' := by
    intros
    ext
    simp
  map_comp' := by
    intros
    ext
    simp

end Functor

end CategoryTheory

namespace CategoryTheory

namespace DifferentialObject

variable (C : Type u) [Category.{v} C]

variable [HasZeroObject C] [HasZeroMorphisms C] [HasShift C ℤ]

open_locale ZeroObject

instance hasZeroObject : HasZeroObject (DifferentialObject C) where
  zero := { x := (0 : C), d := 0 }
  uniqueTo := fun X =>
    ⟨⟨{ f := 0 }⟩, fun f => by
      ext⟩
  uniqueFrom := fun X =>
    ⟨⟨{ f := 0 }⟩, fun f => by
      ext⟩

end DifferentialObject

namespace DifferentialObject

variable (C : Type (u + 1)) [LargeCategory C] [ConcreteCategory C] [HasZeroMorphisms C] [HasShift C ℤ]

instance concreteCategoryOfDifferentialObjects : ConcreteCategory (DifferentialObject C) where
  forget := forget C ⋙ CategoryTheory.forget C

instance : HasForget₂ (DifferentialObject C) C where
  forget₂ := forget C

end DifferentialObject

/-! The category of differential objects itself has a shift functor. -/


namespace DifferentialObject

variable (C : Type u) [Category.{v} C]

variable [HasZeroMorphisms C] [HasShift C ℤ]

noncomputable section

/-- The shift functor on `differential_object C`. -/
@[simps]
def shiftFunctor (n : ℤ) : DifferentialObject C ⥤ DifferentialObject C where
  obj := fun X =>
    { x := X.x⟦n⟧, d := X.d⟦n⟧' ≫ (shiftComm _ _ _).Hom,
      d_squared' := by
        rw [functor.map_comp, category.assoc, shift_comm_hom_comp_assoc, ← functor.map_comp_assoc, X.d_squared,
          functor.map_zero, zero_comp] }
  map := fun X Y f =>
    { f := f.f⟦n⟧',
      comm' := by
        dsimp
        rw [category.assoc, shift_comm_hom_comp, ← functor.map_comp_assoc, f.comm, functor.map_comp_assoc] }
  map_id' := by
    intro X
    ext1
    dsimp
    rw [Functor.map_id]
  map_comp' := by
    intro X Y Z f g
    ext1
    dsimp
    rw [functor.map_comp]

attribute [local instance] endofunctor_monoidal_category Discrete.addMonoidal

attribute [local reducible] endofunctor_monoidal_category Discrete.addMonoidal shift_comm

/-- The shift functor on `differential_object C` is additive. -/
@[simps]
def shiftFunctorAdd (m n : ℤ) : shiftFunctor C (m + n) ≅ shiftFunctor C m ⋙ shiftFunctor C n := by
  refine' nat_iso.of_components (fun X => mk_iso (shift_add X.x _ _) _) _
  · dsimp
    simp only [obj_μ_app, μ_naturality_assoc, μ_naturalityₗ_assoc, μ_inv_hom_app_assoc, category.assoc, obj_μ_inv_app,
      functor.map_comp, μ_inv_naturalityᵣ_assoc]
    simp [opaque_eq_to_iso]
    
  · intro X Y f
    ext
    dsimp
    exact nat_trans.naturality _ _
    

/-- The shift by zero is naturally isomorphic to the identity. -/
@[simps]
def shiftε : 𝟭 (DifferentialObject C) ≅ shiftFunctor C 0 := by
  refine' nat_iso.of_components (fun X => mk_iso ((shift_monoidal_functor C ℤ).εIso.app X.x) _) _
  · dsimp
    simp
    dsimp
    simp
    
  · introv
    ext
    dsimp
    simp
    

instance : HasShift (DifferentialObject C) ℤ :=
  hasShiftMk _ _ { f := shiftFunctor C, ε := shiftε C, μ := fun m n => (shiftFunctorAdd C m n).symm }

end DifferentialObject

end CategoryTheory

