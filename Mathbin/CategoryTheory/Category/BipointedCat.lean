/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Bipointed
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.PointedCat

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

## TODO

Monoidal structure
-/


open CategoryTheory

universe u

variable {α β : Type _}

/-- The category of bipointed types. -/
structure BipointedCat : Type (u + 1) where
  x : Type u
  toProd : X × X
#align Bipointed BipointedCat

namespace BipointedCat

instance : CoeSort BipointedCat (Type _) :=
  ⟨X⟩

attribute [protected] BipointedCat.X

/-- Turns a bipointing into a bipointed type. -/
def of {X : Type _} (to_prod : X × X) : BipointedCat :=
  ⟨X, to_prod⟩
#align Bipointed.of BipointedCat.of

@[simp]
theorem coe_of {X : Type _} (to_prod : X × X) : ↥(of to_prod) = X :=
  rfl
#align Bipointed.coe_of BipointedCat.coe_of

alias of ← _root_.prod.Bipointed
#align prod.Bipointed Prod.bipointed

instance : Inhabited BipointedCat :=
  ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext]
protected structure Hom (X Y : BipointedCat.{u}) : Type u where
  toFun : X → Y
  map_fst : to_fun X.toProd.1 = Y.toProd.1
  map_snd : to_fun X.toProd.2 = Y.toProd.2
#align Bipointed.hom BipointedCat.Hom

namespace Hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps]
def id (X : BipointedCat) : Hom X X :=
  ⟨id, rfl, rfl⟩
#align Bipointed.hom.id BipointedCat.Hom.id

instance (X : BipointedCat) : Inhabited (Hom X X) :=
  ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps]
def comp {X Y Z : BipointedCat.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨g.toFun ∘ f.toFun, by rw [Function.comp_apply, f.map_fst, g.map_fst], by
    rw [Function.comp_apply, f.map_snd, g.map_snd]⟩
#align Bipointed.hom.comp BipointedCat.Hom.comp

end Hom

instance largeCategory : LargeCategory BipointedCat
    where
  Hom := Hom
  id := Hom.id
  comp := @Hom.comp
  id_comp' _ _ _ := Hom.ext _ _ rfl
  comp_id' _ _ _ := Hom.ext _ _ rfl
  assoc' _ _ _ _ _ _ _ := Hom.ext _ _ rfl
#align Bipointed.large_category BipointedCat.largeCategory

instance concreteCategory : ConcreteCategory BipointedCat
    where
  forget :=
    { obj := BipointedCat.X
      map := @Hom.toFun }
  forget_faithful := ⟨@Hom.ext⟩
#align Bipointed.concrete_category BipointedCat.concreteCategory

/-- Swaps the pointed elements of a bipointed type. `prod.swap` as a functor. -/
@[simps]
def swap : BipointedCat ⥤ BipointedCat
    where
  obj X := ⟨X, X.toProd.swap⟩
  map X Y f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Bipointed.swap BipointedCat.swap

/-- The equivalence between `Bipointed` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : BipointedCat ≌ BipointedCat :=
  Equivalence.mk swap swap
    (NatIso.ofComponents
      (fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
    (NatIso.ofComponents
      (fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
#align Bipointed.swap_equiv BipointedCat.swapEquiv

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swap_equiv :=
  rfl
#align Bipointed.swap_equiv_symm BipointedCat.swapEquiv_symm

end BipointedCat

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the second point. -/
def bipointedToPointedFst : BipointedCat ⥤ PointedCat
    where
  obj X := ⟨X, X.toProd.1⟩
  map X Y f := ⟨f.toFun, f.map_fst⟩
#align Bipointed_to_Pointed_fst bipointedToPointedFst

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the first point. -/
def bipointedToPointedSnd : BipointedCat ⥤ PointedCat
    where
  obj X := ⟨X, X.toProd.2⟩
  map X Y f := ⟨f.toFun, f.map_snd⟩
#align Bipointed_to_Pointed_snd bipointedToPointedSnd

@[simp]
theorem bipointedToPointedFst_comp_forget :
    bipointedToPointedFst ⋙ forget PointedCat = forget BipointedCat :=
  rfl
#align Bipointed_to_Pointed_fst_comp_forget bipointedToPointedFst_comp_forget

@[simp]
theorem bipointedToPointedSnd_comp_forget :
    bipointedToPointedSnd ⋙ forget PointedCat = forget BipointedCat :=
  rfl
#align Bipointed_to_Pointed_snd_comp_forget bipointedToPointedSnd_comp_forget

@[simp]
theorem swap_comp_bipointedToPointedFst :
    BipointedCat.swap ⋙ bipointedToPointedFst = bipointedToPointedSnd :=
  rfl
#align swap_comp_Bipointed_to_Pointed_fst swap_comp_bipointedToPointedFst

@[simp]
theorem swap_comp_bipointedToPointedSnd :
    BipointedCat.swap ⋙ bipointedToPointedSnd = bipointedToPointedFst :=
  rfl
#align swap_comp_Bipointed_to_Pointed_snd swap_comp_bipointedToPointedSnd

/-- The functor from `Pointed` to `Bipointed` which bipoints the point. -/
def pointedToBipointed : PointedCat.{u} ⥤ BipointedCat
    where
  obj X := ⟨X, X.point, X.point⟩
  map X Y f := ⟨f.toFun, f.map_point, f.map_point⟩
#align Pointed_to_Bipointed pointedToBipointed

/-- The functor from `Pointed` to `Bipointed` which adds a second point. -/
def pointedToBipointedFst : PointedCat.{u} ⥤ BipointedCat
    where
  obj X := ⟨Option X, X.point, none⟩
  map X Y f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' X := BipointedCat.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := BipointedCat.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Bipointed_fst pointedToBipointedFst

/-- The functor from `Pointed` to `Bipointed` which adds a first point. -/
def pointedToBipointedSnd : PointedCat.{u} ⥤ BipointedCat
    where
  obj X := ⟨Option X, none, X.point⟩
  map X Y f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' X := BipointedCat.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := BipointedCat.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Bipointed_snd pointedToBipointedSnd

@[simp]
theorem pointedToBipointedFst_comp_swap :
    pointedToBipointedFst ⋙ BipointedCat.swap = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Bipointed_fst_comp_swap pointedToBipointedFst_comp_swap

@[simp]
theorem pointedToBipointedSnd_comp_swap :
    pointedToBipointedSnd ⋙ BipointedCat.swap = pointedToBipointedFst :=
  rfl
#align Pointed_to_Bipointed_snd_comp_swap pointedToBipointedSnd_comp_swap

/-- `Bipointed_to_Pointed_fst` is inverse to `Pointed_to_Bipointed`. -/
@[simps]
def pointedToBipointedCompBipointedToPointedFst :
    pointedToBipointed ⋙ bipointedToPointedFst ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩ })
    fun X Y f => rfl
#align Pointed_to_Bipointed_comp_Bipointed_to_Pointed_fst pointedToBipointedCompBipointedToPointedFst

/-- `Bipointed_to_Pointed_snd` is inverse to `Pointed_to_Bipointed`. -/
@[simps]
def pointedToBipointedCompBipointedToPointedSnd :
    pointedToBipointed ⋙ bipointedToPointedSnd ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩ })
    fun X Y f => rfl
#align Pointed_to_Bipointed_comp_Bipointed_to_Pointed_snd pointedToBipointedCompBipointedToPointedSnd

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_fst` and `Bipointed_to_Pointed_fst`.
-/
def pointedToBipointedFstBipointedToPointedFstAdjunction :
    pointedToBipointedFst ⊣ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by
            ext
            cases x
            exact f.map_snd.symm
            rfl
          right_inv := fun f => PointedCat.Hom.ext _ _ rfl }
      hom_equiv_naturality_left_symm' := fun X' X Y f g =>
        by
        ext
        cases x <;> rfl }
#align Pointed_to_Bipointed_fst_Bipointed_to_Pointed_fst_adjunction pointedToBipointedFstBipointedToPointedFstAdjunction

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_snd` and `Bipointed_to_Pointed_snd`.
-/
def pointedToBipointedSndBipointedToPointedSndAdjunction :
    pointedToBipointedSnd ⊣ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by
            ext
            cases x
            exact f.map_fst.symm
            rfl
          right_inv := fun f => PointedCat.Hom.ext _ _ rfl }
      hom_equiv_naturality_left_symm' := fun X' X Y f g =>
        by
        ext
        cases x <;> rfl }
#align Pointed_to_Bipointed_snd_Bipointed_to_Pointed_snd_adjunction pointedToBipointedSndBipointedToPointedSndAdjunction

