/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module category_theory.category.Twop
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Category.BipointedCat
import Mathbin.Data.TwoPointing

/-!
# The category of two-pointed types

This defines `Twop`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of two-pointed types. -/
structure TwopCat : Type (u + 1) where
  x : Type u
  toTwoPointing : TwoPointing X
#align Twop TwopCat

namespace TwopCat

instance : CoeSort TwopCat (Type _) :=
  ⟨X⟩

attribute [protected] TwopCat.X

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type _} (to_two_pointing : TwoPointing X) : TwopCat :=
  ⟨X, to_two_pointing⟩
#align Twop.of TwopCat.of

@[simp]
theorem coe_of {X : Type _} (to_two_pointing : TwoPointing X) : ↥(of to_two_pointing) = X :=
  rfl
#align Twop.coe_of TwopCat.coe_of

alias of ← _root_.two_pointing.Twop

instance : Inhabited TwopCat :=
  ⟨of TwoPointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
def toBipointed (X : TwopCat) : BipointedCat :=
  X.toTwoPointing.toProd.BipointedCat
#align Twop.to_Bipointed TwopCat.toBipointed

@[simp]
theorem coe_to_Bipointed (X : TwopCat) : ↥X.toBipointed = ↥X :=
  rfl
#align Twop.coe_to_Bipointed TwopCat.coe_to_Bipointed

instance largeCategory : LargeCategory TwopCat :=
  InducedCategory.category toBipointed
#align Twop.large_category TwopCat.largeCategory

instance concreteCategory : ConcreteCategory TwopCat :=
  InducedCategory.concreteCategory toBipointed
#align Twop.concrete_category TwopCat.concreteCategory

instance hasForgetToBipointed : HasForget₂ TwopCat BipointedCat :=
  InducedCategory.hasForget₂ toBipointed
#align Twop.has_forget_to_Bipointed TwopCat.hasForgetToBipointed

/-- Swaps the pointed elements of a two-pointed type. `two_pointing.swap` as a functor. -/
@[simps]
def swap : TwopCat ⥤ TwopCat where 
  obj X := ⟨X, X.toTwoPointing.swap⟩
  map X Y f := ⟨f.toFun, f.map_snd, f.map_fst⟩
#align Twop.swap TwopCat.swap

/-- The equivalence between `Twop` and itself induced by `prod.swap` both ways. -/
@[simps]
def swapEquiv : TwopCat ≌ TwopCat :=
  Equivalence.mk swap swap
    ((NatIso.ofComponents fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
    ((NatIso.ofComponents fun X =>
        { Hom := ⟨id, rfl, rfl⟩
          inv := ⟨id, rfl, rfl⟩ })
      fun X Y f => rfl)
#align Twop.swap_equiv TwopCat.swapEquiv

@[simp]
theorem swap_equiv_symm : swapEquiv.symm = swap_equiv :=
  rfl
#align Twop.swap_equiv_symm TwopCat.swap_equiv_symm

end TwopCat

@[simp]
theorem Twop_swap_comp_forget_to_Bipointed :
    TwopCat.swap ⋙ forget₂ TwopCat BipointedCat =
      forget₂ TwopCat BipointedCat ⋙ BipointedCat.swap :=
  rfl
#align Twop_swap_comp_forget_to_Bipointed Twop_swap_comp_forget_to_Bipointed

/-- The functor from `Pointed` to `Twop` which adds a second point. -/
@[simps]
def pointedToTwopFst :
    PointedCat.{u} ⥤
      TwopCat where 
  obj X := ⟨Option X, ⟨X.point, none⟩, some_ne_none _⟩
  map X Y f := ⟨Option.map f.toFun, congr_arg _ f.map_point, rfl⟩
  map_id' X := BipointedCat.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := BipointedCat.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_fst pointedToTwopFst

/-- The functor from `Pointed` to `Twop` which adds a first point. -/
@[simps]
def pointedToTwopSnd :
    PointedCat.{u} ⥤
      TwopCat where 
  obj X := ⟨Option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩
  map X Y f := ⟨Option.map f.toFun, rfl, congr_arg _ f.map_point⟩
  map_id' X := BipointedCat.Hom.ext _ _ Option.map_id
  map_comp' X Y Z f g := BipointedCat.Hom.ext _ _ (Option.map_comp_map _ _).symm
#align Pointed_to_Twop_snd pointedToTwopSnd

@[simp]
theorem Pointed_to_Twop_fst_comp_swap : pointedToTwopFst ⋙ TwopCat.swap = pointedToTwopSnd :=
  rfl
#align Pointed_to_Twop_fst_comp_swap Pointed_to_Twop_fst_comp_swap

@[simp]
theorem Pointed_to_Twop_snd_comp_swap : pointedToTwopSnd ⋙ TwopCat.swap = pointedToTwopFst :=
  rfl
#align Pointed_to_Twop_snd_comp_swap Pointed_to_Twop_snd_comp_swap

@[simp]
theorem Pointed_to_Twop_fst_comp_forget_to_Bipointed :
    pointedToTwopFst ⋙ forget₂ TwopCat BipointedCat = pointedToBipointedFst :=
  rfl
#align Pointed_to_Twop_fst_comp_forget_to_Bipointed Pointed_to_Twop_fst_comp_forget_to_Bipointed

@[simp]
theorem Pointed_to_Twop_snd_comp_forget_to_Bipointed :
    pointedToTwopSnd ⋙ forget₂ TwopCat BipointedCat = pointedToBipointedSnd :=
  rfl
#align Pointed_to_Twop_snd_comp_forget_to_Bipointed Pointed_to_Twop_snd_comp_forget_to_Bipointed

/-- Adding a second point is left adjoint to forgetting the second point. -/
def pointedToTwopFstForgetCompBipointedToPointedFstAdjunction :
    pointedToTwopFst ⊣ forget₂ TwopCat BipointedCat ⋙ bipointedToPointedFst :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_fst⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.2 f.toFun, f.map_point, rfl⟩
          left_inv := fun f => by 
            ext
            cases x
            exact f.map_snd.symm
            rfl
          right_inv := fun f => PointedCat.Hom.ext _ _ rfl }
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext
        cases x <;> rfl }
#align
  Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction pointedToTwopFstForgetCompBipointedToPointedFstAdjunction

/-- Adding a first point is left adjoint to forgetting the first point. -/
def pointedToTwopSndForgetCompBipointedToPointedSndAdjunction :
    pointedToTwopSnd ⊣ forget₂ TwopCat BipointedCat ⋙ bipointedToPointedSnd :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => ⟨f.toFun ∘ Option.some, f.map_snd⟩
          invFun := fun f => ⟨fun o => o.elim Y.toTwoPointing.toProd.1 f.toFun, rfl, f.map_point⟩
          left_inv := fun f => by 
            ext
            cases x
            exact f.map_fst.symm
            rfl
          right_inv := fun f => PointedCat.Hom.ext _ _ rfl }
      hom_equiv_naturality_left_symm' := fun X' X Y f g => by
        ext
        cases x <;> rfl }
#align
  Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction pointedToTwopSndForgetCompBipointedToPointedSndAdjunction

