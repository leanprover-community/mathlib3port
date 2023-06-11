/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Twop
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.Bipointed
import Mathbin.Data.TwoPointing

/-!
# The category of two-pointed types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This defines `Twop`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

#print TwoP /-
/-- The category of two-pointed types. -/
structure TwoP : Type (u + 1) where
  pt : Type u
  toTwoPointing : TwoPointing X
#align Twop TwoP
-/

namespace TwoP

instance : CoeSort TwoP (Type _) :=
  ⟨X⟩

attribute [protected] TwoP.X

#print TwoP.of /-
/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type _} (to_two_pointing : TwoPointing X) : TwoP :=
  ⟨X, to_two_pointing⟩
#align Twop.of TwoP.of
-/

#print TwoP.coe_of /-
@[simp]
theorem coe_of {X : Type _} (to_two_pointing : TwoPointing X) : ↥(of to_two_pointing) = X :=
  rfl
#align Twop.coe_of TwoP.coe_of
-/

alias of ← _root_.two_pointing.Twop
#align two_pointing.Twop TwoPointing.TwoP

instance : Inhabited TwoP :=
  ⟨of TwoPointing.bool⟩

#print TwoP.toBipointed /-
/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
def toBipointed (X : TwoP) : Bipointed :=
  X.toTwoPointing.toProd.Bipointed
#align Twop.to_Bipointed TwoP.toBipointed
-/

#print TwoP.coe_toBipointed /-
@[simp]
theorem coe_toBipointed (X : TwoP) : ↥X.toBipointed = ↥X :=
  rfl
#align Twop.coe_to_Bipointed TwoP.coe_toBipointed
-/

#print TwoP.largeCategory /-
instance largeCategory : LargeCategory TwoP :=
  InducedCategory.category toBipointed
#align Twop.large_category TwoP.largeCategory
-/

#print TwoP.concreteCategory /-
instance concreteCategory : ConcreteCategory TwoP :=
  InducedCategory.concreteCategory toBipointed
#align Twop.concrete_category TwoP.concreteCategory
-/

instance hasForgetToBipointed : HasForget₂ TwoP Bipointed :=
  InducedCategory.hasForget₂ toBipointed
#align Twop.has_forget_to_Bipointed TwoP.hasForgetToBipointed

#print TwoP.swap /-
/-- Swaps the pointed elements of a two-pointed type. `two_pointing.swap` as a functor. -/
@[simps]
def swap : TwoP ⥤ TwoP where
  obj X := ⟨X, X.toTwoPointing.symm⟩
  map X Y f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Twop.swap TwoP.swap
-/

/-- The equivalence between `Twop` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : TwoP ≌ TwoP :=
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
#align Twop.swap_equiv TwoP.swapEquiv

@[simp]
theorem swapEquiv_symm : swapEquiv.symm = swapEquiv :=
  rfl
#align Twop.swap_equiv_symm TwoP.swapEquiv_symm

end TwoP

#print TwoP_swap_comp_forget_to_Bipointed /-
@[simp]
theorem TwoP_swap_comp_forget_to_Bipointed :
    TwoP.swap ⋙ forget₂ TwoP Bipointed = forget₂ TwoP Bipointed ⋙ Bipointed.swap :=
  rfl
#align Twop_swap_comp_forget_to_Bipointed TwoP_swap_comp_forget_to_Bipointed
-/

#print pointedToTwoPFst /-
/-- The functor from `Pointed` to `Twop` which adds a second point. -/
@[simps]
def pointedToTwoPFst : Pointed.{u} ⥤ TwoP
    where
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map X Y f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_fst pointedToTwoPFst
-/

#print pointedToTwoPSnd /-
/-- The functor from `Pointed` to `Twop` which adds a first point. -/
@[simps]
def pointedToTwoPSnd : Pointed.{u} ⥤ TwoP
    where
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map X Y f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' X := Bipointed.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := Bipointed.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_snd pointedToTwoPSnd
-/

#print pointedToTwoPFst_comp_swap /-
@[simp]
theorem pointedToTwoPFst_comp_swap : pointedToTwoPFst ⋙ TwoP.swap = pointedToTwoPSnd :=
  rfl
#align Pointed_to_Twop_fst_comp_swap pointedToTwoPFst_comp_swap
-/

#print pointedToTwoPSnd_comp_swap /-
@[simp]
theorem pointedToTwoPSnd_comp_swap : pointedToTwoPSnd ⋙ TwoP.swap = pointedToTwoPFst :=
  rfl
#align Pointed_to_Twop_snd_comp_swap pointedToTwoPSnd_comp_swap
-/

#print pointedToTwoPFst_comp_forget_to_bipointed /-
@[simp]
theorem pointedToTwoPFst_comp_forget_to_bipointed :
    pointedToTwoPFst ⋙ forget₂ TwoP Bipointed = pointedToBipointedFst :=
  rfl
#align Pointed_to_Twop_fst_comp_forget_to_Bipointed pointedToTwoPFst_comp_forget_to_bipointed
-/

#print pointedToTwoPSnd_comp_forget_to_bipointed /-
@[simp]
theorem pointedToTwoPSnd_comp_forget_to_bipointed :
    pointedToTwoPSnd ⋙ forget₂ TwoP Bipointed = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Twop_snd_comp_forget_to_Bipointed pointedToTwoPSnd_comp_forget_to_bipointed
-/

#print pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction /-
/-- Adding a second point is left adjoint to forgetting the second point. -/
def pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwoPFst ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by ext; cases x; exact f.map_snd.symm; rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun X' X Y f g => by ext; cases x <;> rfl }
#align Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction pointedToTwoPFstForgetCompBipointedToPointedFstAdjunction
-/

#print pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction /-
/-- Adding a first point is left adjoint to forgetting the first point. -/
def pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwoPSnd ⊣ forget₂ TwoP Bipointed ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by ext; cases x; exact f.map_fst.symm; rfl
          right_inv := fun f => Pointed.Hom.ext _ _ rfl }
      homEquiv_naturality_left_symm := fun X' X Y f g => by ext; cases x <;> rfl }
#align Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction pointedToTwoPSndForgetCompBipointedToPointedSndAdjunction
-/

