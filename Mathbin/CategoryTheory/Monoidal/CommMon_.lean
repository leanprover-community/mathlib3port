/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import CategoryTheory.Monoidal.Braided.Basic
import CategoryTheory.Monoidal.Mon_

#align_import category_theory.monoidal.CommMon_ from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!
# The category of commutative monoids in a braided monoidal category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


universe v₁ v₂ u₁ u₂ u

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C] [BraidedCategory.{v₁} C]

#print CommMon_ /-
/-- A commutative monoid object internal to a monoidal category.
-/
structure CommMon_ extends Mon_ C where
  mul_comm' : (β_ _ _).Hom ≫ mul = mul := by obviously
#align CommMon_ CommMon_
-/

attribute [simp, reassoc] CommMon_.mul_comm

namespace CommMon_

#print CommMon_.trivial /-
/-- The trivial commutative monoid object. We later show this is initial in `CommMon_ C`.
-/
@[simps]
def trivial : CommMon_ C :=
  { Mon_.trivial C with mul_comm' := by dsimp; rw [braiding_left_unitor, unitors_equal] }
#align CommMon_.trivial CommMon_.trivial
-/

instance : Inhabited (CommMon_ C) :=
  ⟨trivial C⟩

variable {C} {M : CommMon_ C}

instance : Category (CommMon_ C) :=
  InducedCategory.category CommMon_.toMon_

#print CommMon_.id_hom /-
@[simp]
theorem id_hom (A : CommMon_ C) : Mon_.Hom.hom (𝟙 A) = 𝟙 A.pt :=
  rfl
#align CommMon_.id_hom CommMon_.id_hom
-/

#print CommMon_.comp_hom /-
@[simp]
theorem comp_hom {R S T : CommMon_ C} (f : R ⟶ S) (g : S ⟶ T) :
    Mon_.Hom.hom (f ≫ g) = f.Hom ≫ g.Hom :=
  rfl
#align CommMon_.comp_hom CommMon_.comp_hom
-/

section

variable (C)

#print CommMon_.forget₂Mon_ /-
/-- The forgetful functor from commutative monoid objects to monoid objects. -/
def forget₂Mon_ : CommMon_ C ⥤ Mon_ C :=
  inducedFunctor CommMon_.toMon_
deriving CategoryTheory.Functor.Full, CategoryTheory.Functor.Faithful
#align CommMon_.forget₂_Mon_ CommMon_.forget₂Mon_
-/

#print CommMon_.forget₂_Mon_obj_one /-
@[simp]
theorem forget₂_Mon_obj_one (A : CommMon_ C) : ((forget₂Mon_ C).obj A).one = A.one :=
  rfl
#align CommMon_.forget₂_Mon_obj_one CommMon_.forget₂_Mon_obj_one
-/

#print CommMon_.forget₂_Mon_obj_mul /-
@[simp]
theorem forget₂_Mon_obj_mul (A : CommMon_ C) : ((forget₂Mon_ C).obj A).mul = A.mul :=
  rfl
#align CommMon_.forget₂_Mon_obj_mul CommMon_.forget₂_Mon_obj_mul
-/

#print CommMon_.forget₂_Mon_map_hom /-
@[simp]
theorem forget₂_Mon_map_hom {A B : CommMon_ C} (f : A ⟶ B) : ((forget₂Mon_ C).map f).Hom = f.Hom :=
  rfl
#align CommMon_.forget₂_Mon_map_hom CommMon_.forget₂_Mon_map_hom
-/

end

#print CommMon_.uniqueHomFromTrivial /-
instance uniqueHomFromTrivial (A : CommMon_ C) : Unique (trivial C ⟶ A) :=
  Mon_.uniqueHomFromTrivial A.toMon_
#align CommMon_.unique_hom_from_trivial CommMon_.uniqueHomFromTrivial
-/

open CategoryTheory.Limits

instance : HasInitial (CommMon_ C) :=
  hasInitial_of_unique (trivial C)

end CommMon_

namespace CategoryTheory.LaxBraidedFunctor

variable {C} {D : Type u₂} [Category.{v₂} D] [MonoidalCategory.{v₂} D] [BraidedCategory.{v₂} D]

#print CategoryTheory.LaxBraidedFunctor.mapCommMon /-
/-- A lax braided functor takes commutative monoid objects to commutative monoid objects.

That is, a lax braided functor `F : C ⥤ D` induces a functor `CommMon_ C ⥤ CommMon_ D`.
-/
@[simps]
def mapCommMon (F : LaxBraidedFunctor C D) : CommMon_ C ⥤ CommMon_ D
    where
  obj A :=
    { F.toLaxMonoidalFunctor.mapMon.obj A.toMon_ with
      mul_comm' := by
        dsimp
        have := F.braided
        slice_lhs 1 2 => rw [← this]
        slice_lhs 2 3 => rw [← CategoryTheory.Functor.map_comp, A.mul_comm] }
  map A B f := F.toLaxMonoidalFunctor.mapMon.map f
#align category_theory.lax_braided_functor.map_CommMon CategoryTheory.LaxBraidedFunctor.mapCommMon
-/

variable (C) (D)

#print CategoryTheory.LaxBraidedFunctor.mapCommMonFunctor /-
/-- `map_CommMon` is functorial in the lax braided functor. -/
def mapCommMonFunctor : LaxBraidedFunctor C D ⥤ CommMon_ C ⥤ CommMon_ D
    where
  obj := mapCommMon
  map F G α := { app := fun A => { Hom := α.app A.pt } }
#align category_theory.lax_braided_functor.map_CommMon_functor CategoryTheory.LaxBraidedFunctor.mapCommMonFunctor
-/

end CategoryTheory.LaxBraidedFunctor

namespace CommMon_

open CategoryTheory.LaxBraidedFunctor

namespace EquivLaxBraidedFunctorPunit

#print CommMon_.EquivLaxBraidedFunctorPUnit.laxBraidedToCommMon /-
/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def laxBraidedToCommMon : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ⥤ CommMon_ C
    where
  obj F := (F.mapCommMon : CommMon_ _ ⥤ CommMon_ C).obj (trivial (Discrete PUnit))
  map F G α := ((mapCommMonFunctor (Discrete PUnit) C).map α).app _
#align CommMon_.equiv_lax_braided_functor_punit.lax_braided_to_CommMon CommMon_.EquivLaxBraidedFunctorPUnit.laxBraidedToCommMon
-/

#print CommMon_.EquivLaxBraidedFunctorPUnit.commMonToLaxBraided /-
/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def commMonToLaxBraided : CommMon_ C ⥤ LaxBraidedFunctor (Discrete PUnit.{u + 1}) C
    where
  obj A :=
    { obj := fun _ => A.pt
      map := fun _ _ _ => 𝟙 _
      ε := A.one
      μ := fun _ _ => A.mul
      map_id' := fun _ => rfl
      map_comp' := fun _ _ _ _ _ => (Category.id_comp (𝟙 A.pt)).symm }
  map A B f :=
    { app := fun _ => f.Hom
      naturality' := fun _ _ _ => by dsimp; rw [category.id_comp, category.comp_id]
      unit' := f.OneHom
      tensor' := fun _ _ => f.MulHom }
#align CommMon_.equiv_lax_braided_functor_punit.CommMon_to_lax_braided CommMon_.EquivLaxBraidedFunctorPUnit.commMonToLaxBraided
-/

attribute [local tidy] tactic.discrete_cases

attribute [local simp] eq_to_iso_map

#print CommMon_.EquivLaxBraidedFunctorPUnit.unitIso /-
/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def unitIso :
    𝟭 (LaxBraidedFunctor (Discrete PUnit.{u + 1}) C) ≅
      laxBraidedToCommMon C ⋙ commMonToLaxBraided C :=
  NatIso.ofComponents
    (fun F =>
      LaxBraidedFunctor.mkIso
        (MonoidalNatIso.ofComponents
          (fun _ => F.toLaxMonoidalFunctor.toFunctor.mapIso (eqToIso (by ext))) (by tidy) (by tidy)
          (by tidy)))
    (by tidy)
#align CommMon_.equiv_lax_braided_functor_punit.unit_iso CommMon_.EquivLaxBraidedFunctorPUnit.unitIso
-/

#print CommMon_.EquivLaxBraidedFunctorPUnit.counitIso /-
/-- Implementation of `CommMon_.equiv_lax_braided_functor_punit`. -/
@[simps]
def counitIso : commMonToLaxBraided C ⋙ laxBraidedToCommMon C ≅ 𝟭 (CommMon_ C) :=
  NatIso.ofComponents
    (fun F =>
      { Hom := { Hom := 𝟙 _ }
        inv := { Hom := 𝟙 _ } })
    (by tidy)
#align CommMon_.equiv_lax_braided_functor_punit.counit_iso CommMon_.EquivLaxBraidedFunctorPUnit.counitIso
-/

end EquivLaxBraidedFunctorPunit

open EquivLaxBraidedFunctorPunit

attribute [local simp] eq_to_iso_map

#print CommMon_.equivLaxBraidedFunctorPUnit /-
/-- Commutative monoid objects in `C` are "just" braided lax monoidal functors from the trivial
braided monoidal category to `C`.
-/
@[simps]
def equivLaxBraidedFunctorPUnit : LaxBraidedFunctor (Discrete PUnit.{u + 1}) C ≌ CommMon_ C
    where
  Functor := laxBraidedToCommMon C
  inverse := commMonToLaxBraided C
  unitIso := unitIso C
  counitIso := counitIso C
#align CommMon_.equiv_lax_braided_functor_punit CommMon_.equivLaxBraidedFunctorPUnit
-/

end CommMon_

