/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin

! This file was ported from Lean 3 source module analysis.normed.group.SemiNormedGroup.completion
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.SemiNormedGroupCat
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor
import Mathbin.Analysis.Normed.Group.HomCompletion

/-!
# Completions of normed groups

This file contains an API for completions of seminormed groups (basic facts about
objects and morphisms).

## Main definitions

- `SemiNormedGroup.Completion : SemiNormedGroup ⥤ SemiNormedGroup` : the completion of a
  seminormed group (defined as a functor on `SemiNormedGroup` to itself).
- `SemiNormedGroup.Completion.lift (f : V ⟶ W) : (Completion.obj V ⟶ W)` : a normed group hom
  from `V` to complete `W` extends ("lifts") to a seminormed group hom from the completion of
  `V` to `W`.

## Projects

1. Construct the category of complete seminormed groups, say `CompleteSemiNormedGroup`
  and promote the `Completion` functor below to a functor landing in this category.
2. Prove that the functor `Completion : SemiNormedGroup ⥤ CompleteSemiNormedGroup`
  is left adjoint to the forgetful functor.

-/


noncomputable section

universe u

open UniformSpace MulOpposite CategoryTheory NormedAddGroupHom

namespace SemiNormedGroupCat

/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def completion : SemiNormedGroupCat.{u} ⥤ SemiNormedGroupCat.{u}
    where
  obj V := SemiNormedGroupCat.of (completion V)
  map V W f := f.Completion
  map_id' V := completion_id
  map_comp' U V W f g := (completion_comp f g).symm
#align SemiNormedGroup.Completion SemiNormedGroupCat.completion

instance Completion_complete_space {V : SemiNormedGroupCat} : CompleteSpace (completion.obj V) :=
  Completion.complete_space _
#align SemiNormedGroup.Completion_complete_space SemiNormedGroupCat.Completion_complete_space

/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def completion.incl {V : SemiNormedGroupCat} : V ⟶ completion.obj V
    where
  toFun v := (v : completion V)
  map_add' := Completion.coe_add
  bound' := ⟨1, fun v => by simp⟩
#align SemiNormedGroup.Completion.incl SemiNormedGroupCat.completion.incl

theorem completion.norm_incl_eq {V : SemiNormedGroupCat} {v : V} : ‖completion.incl v‖ = ‖v‖ := by
  simp
#align SemiNormedGroup.Completion.norm_incl_eq SemiNormedGroupCat.completion.norm_incl_eq

theorem completion.map_norm_noninc {V W : SemiNormedGroupCat} {f : V ⟶ W} (hf : f.NormNoninc) :
    (completion.map f).NormNoninc :=
  NormedAddGroupHom.NormNoninc.norm_noninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f).le.trans <|
      NormedAddGroupHom.NormNoninc.norm_noninc_iff_norm_le_one.1 hf
#align SemiNormedGroup.Completion.map_norm_noninc SemiNormedGroupCat.completion.map_norm_noninc

/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def completion.mapHom (V W : SemiNormedGroupCat.{u}) :
    (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  (AddMonoidHom.mk' (CategoryTheory.Functor.map completion)) fun f g => f.completion_add g
#align SemiNormedGroup.Completion.map_hom SemiNormedGroupCat.completion.mapHom

@[simp]
theorem completion.map_zero (V W : SemiNormedGroupCat) : completion.map (0 : V ⟶ W) = 0 :=
  (completion.mapHom V W).map_zero
#align SemiNormedGroup.Completion.map_zero SemiNormedGroupCat.completion.map_zero

instance : Preadditive SemiNormedGroupCat.{u}
    where
  homGroup P Q := inferInstance
  add_comp' := by
    intros
    ext
    simp only [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, map_add]
  comp_add' := by
    intros
    ext
    simp only [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, map_add]

instance : Functor.Additive completion where map_add' X Y := (completion.mapHom _ _).map_add

/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def completion.lift {V W : SemiNormedGroupCat} [CompleteSpace W] [SeparatedSpace W] (f : V ⟶ W) :
    completion.obj V ⟶ W where
  toFun := f.extension
  map_add' := f.extension.toAddMonoidHom.map_add'
  bound' := f.extension.bound'
#align SemiNormedGroup.Completion.lift SemiNormedGroupCat.completion.lift

theorem completion.lift_comp_incl {V W : SemiNormedGroupCat} [CompleteSpace W] [SeparatedSpace W]
    (f : V ⟶ W) : Completion.incl ≫ completion.lift f = f :=
  by
  ext
  apply NormedAddGroupHom.extension_coe
#align SemiNormedGroup.Completion.lift_comp_incl SemiNormedGroupCat.completion.lift_comp_incl

theorem completion.lift_unique {V W : SemiNormedGroupCat} [CompleteSpace W] [SeparatedSpace W]
    (f : V ⟶ W) (g : completion.obj V ⟶ W) : Completion.incl ≫ g = f → g = completion.lift f :=
  fun h => (NormedAddGroupHom.extension_unique _ fun v => ((ext_iff.1 h) v).symm).symm
#align SemiNormedGroup.Completion.lift_unique SemiNormedGroupCat.completion.lift_unique

end SemiNormedGroupCat

