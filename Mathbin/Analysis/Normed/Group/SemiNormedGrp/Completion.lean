/-
Copyright (c) 2021 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Johan Commelin
-/
import Analysis.Normed.Group.SemiNormedGrp
import CategoryTheory.Preadditive.AdditiveFunctor
import Analysis.Normed.Group.HomCompletion

#align_import analysis.normed.group.SemiNormedGroup.completion from "leanprover-community/mathlib"@"2fe465deb81bcd7ccafa065bb686888a82f15372"

/-!
# Completions of normed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

namespace SemiNormedGrp

#print SemiNormedGrp.completion /-
/-- The completion of a seminormed group, as an endofunctor on `SemiNormedGroup`. -/
@[simps]
def completion : SemiNormedGrp.{u} ⥤ SemiNormedGrp.{u}
    where
  obj V := SemiNormedGrp.of (completion V)
  map V W f := f.Completion
  map_id'' V := completion_id
  map_comp' U V W f g := (completion_comp f g).symm
#align SemiNormedGroup.Completion SemiNormedGrp.completion
-/

#print SemiNormedGrp.completion_completeSpace /-
instance completion_completeSpace {V : SemiNormedGrp} : CompleteSpace (completion.obj V) :=
  Completion.completeSpace _
#align SemiNormedGroup.Completion_complete_space SemiNormedGrp.completion_completeSpace
-/

#print SemiNormedGrp.completion.incl /-
/-- The canonical morphism from a seminormed group `V` to its completion. -/
@[simps]
def completion.incl {V : SemiNormedGrp} : V ⟶ completion.obj V
    where
  toFun v := (v : completion V)
  map_add' := Completion.coe_add
  bound' := ⟨1, fun v => by simp⟩
#align SemiNormedGroup.Completion.incl SemiNormedGrp.completion.incl
-/

#print SemiNormedGrp.completion.norm_incl_eq /-
theorem completion.norm_incl_eq {V : SemiNormedGrp} {v : V} : ‖completion.incl v‖ = ‖v‖ := by simp
#align SemiNormedGroup.Completion.norm_incl_eq SemiNormedGrp.completion.norm_incl_eq
-/

#print SemiNormedGrp.completion.map_normNoninc /-
theorem completion.map_normNoninc {V W : SemiNormedGrp} {f : V ⟶ W} (hf : f.NormNoninc) :
    (completion.map f).NormNoninc :=
  NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.2 <|
    (NormedAddGroupHom.norm_completion f).le.trans <|
      NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.1 hf
#align SemiNormedGroup.Completion.map_norm_noninc SemiNormedGrp.completion.map_normNoninc
-/

#print SemiNormedGrp.completion.mapHom /-
/-- Given a normed group hom `V ⟶ W`, this defines the associated morphism
from the completion of `V` to the completion of `W`.
The difference from the definition obtained from the functoriality of completion is in that the
map sending a morphism `f` to the associated morphism of completions is itself additive. -/
def completion.mapHom (V W : SemiNormedGrp.{u}) :
    (V ⟶ W) →+ (completion.obj V ⟶ completion.obj W) :=
  AddMonoidHom.mk' (CategoryTheory.Functor.map completion) fun f g => f.completion_add g
#align SemiNormedGroup.Completion.map_hom SemiNormedGrp.completion.mapHom
-/

#print SemiNormedGrp.completion.map_zero /-
@[simp]
theorem completion.map_zero (V W : SemiNormedGrp) : completion.map (0 : V ⟶ W) = 0 :=
  (completion.mapHom V W).map_zero
#align SemiNormedGroup.Completion.map_zero SemiNormedGrp.completion.map_zero
-/

instance : Preadditive SemiNormedGrp.{u}
    where
  homGroup P Q := inferInstance
  add_comp := by
    intros; ext
    simp only [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, map_add]
  comp_add := by
    intros; ext
    simp only [NormedAddGroupHom.add_apply, CategoryTheory.comp_apply, map_add]

instance : Functor.Additive completion where map_add' X Y := (completion.mapHom _ _).map_add

#print SemiNormedGrp.completion.lift /-
/-- Given a normed group hom `f : V → W` with `W` complete, this provides a lift of `f` to
the completion of `V`. The lemmas `lift_unique` and `lift_comp_incl` provide the api for the
universal property of the completion. -/
def completion.lift {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.obj V ⟶ W where
  toFun := f.extension
  map_add' := f.extension.toAddMonoidHom.map_add'
  bound' := f.extension.bound'
#align SemiNormedGroup.Completion.lift SemiNormedGrp.completion.lift
-/

#print SemiNormedGrp.completion.lift_comp_incl /-
theorem completion.lift_comp_incl {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W) :
    completion.incl ≫ completion.lift f = f := by ext; apply NormedAddGroupHom.extension_coe
#align SemiNormedGroup.Completion.lift_comp_incl SemiNormedGrp.completion.lift_comp_incl
-/

#print SemiNormedGrp.completion.lift_unique /-
theorem completion.lift_unique {V W : SemiNormedGrp} [CompleteSpace W] [T0Space W] (f : V ⟶ W)
    (g : completion.obj V ⟶ W) : completion.incl ≫ g = f → g = completion.lift f := fun h =>
  (NormedAddGroupHom.extension_unique _ fun v => ((ext_iff.1 h) v).symm).symm
#align SemiNormedGroup.Completion.lift_unique SemiNormedGrp.completion.lift_unique
-/

end SemiNormedGrp

