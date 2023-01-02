/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.Mod
! leanprover-community/mathlib commit 1e05171a5e8cf18d98d9cf7b207540acb044acae
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Mon_

/-!
# The category of module objects over a monoid object.
-/


universe v₁ v₂ u₁ u₂

open CategoryTheory

open CategoryTheory.MonoidalCategory

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory.{v₁} C]

variable {C}

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A module object for a monoid object, all internal to some monoidal category. -/
structure ModCat (A : Mon_ C) where
  x : C
  act : A.x ⊗ X ⟶ X
  one_act' : (A.one ⊗ 𝟙 X) ≫ act = (λ_ X).Hom := by obviously
  assoc' : (A.mul ⊗ 𝟙 X) ≫ act = (α_ A.x A.x X).Hom ≫ (𝟙 A.x ⊗ act) ≫ act := by obviously
#align Mod ModCat

restate_axiom ModCat.one_act'

restate_axiom ModCat.assoc'

attribute [simp, reassoc.1] ModCat.one_act ModCat.assoc

namespace ModCat

variable {A : Mon_ C} (M : ModCat A)

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem assoc_flip : (𝟙 A.x ⊗ M.act) ≫ M.act = (α_ A.x A.x M.x).inv ≫ (A.mul ⊗ 𝟙 M.x) ≫ M.act := by
  simp
#align Mod.assoc_flip ModCat.assoc_flip

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of module objects. -/
@[ext]
structure Hom (M N : ModCat A) where
  Hom : M.x ⟶ N.x
  act_hom' : M.act ≫ hom = (𝟙 A.x ⊗ hom) ≫ N.act := by obviously
#align Mod.hom ModCat.Hom

restate_axiom hom.act_hom'

attribute [simp, reassoc.1] hom.act_hom

/-- The identity morphism on a module object. -/
@[simps]
def id (M : ModCat A) : Hom M M where Hom := 𝟙 M.x
#align Mod.id ModCat.id

instance homInhabited (M : ModCat A) : Inhabited (Hom M M) :=
  ⟨id M⟩
#align Mod.hom_inhabited ModCat.homInhabited

/-- Composition of module object morphisms. -/
@[simps]
def comp {M N O : ModCat A} (f : Hom M N) (g : Hom N O) : Hom M O where Hom := f.Hom ≫ g.Hom
#align Mod.comp ModCat.comp

instance : Category (ModCat A) where
  Hom M N := Hom M N
  id := id
  comp M N O f g := comp f g

@[simp]
theorem id_hom' (M : ModCat A) : (𝟙 M : Hom M M).Hom = 𝟙 M.x :=
  rfl
#align Mod.id_hom' ModCat.id_hom'

@[simp]
theorem comp_hom' {M N K : ModCat A} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : Hom M K).Hom = f.Hom ≫ g.Hom :=
  rfl
#align Mod.comp_hom' ModCat.comp_hom'

variable (A)

/-- A monoid object as a module over itself. -/
@[simps]
def regular : ModCat A where
  x := A.x
  act := A.mul
#align Mod.regular ModCat.regular

instance : Inhabited (ModCat A) :=
  ⟨regular A⟩

/-- The forgetful functor from module objects to the ambient category. -/
def forget : ModCat A ⥤ C where
  obj A := A.x
  map A B f := f.Hom
#align Mod.forget ModCat.forget

open CategoryTheory.MonoidalCategory

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- A morphism of monoid objects induces a "restriction" or "comap" functor
between the categories of module objects.
-/
@[simps]
def comap {A B : Mon_ C} (f : A ⟶ B) : ModCat B ⥤ ModCat A
    where
  obj M :=
    { x := M.x
      act := (f.Hom ⊗ 𝟙 M.x) ≫ M.act
      one_act' := by
        slice_lhs 1 2 => rw [← comp_tensor_id]
        rw [f.one_hom, one_act]
      assoc' :=
        by
        -- oh, for homotopy.io in a widget!
        slice_rhs 2 3 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        rw [id_tensor_comp]
        slice_rhs 4 5 => rw [ModCat.assoc_flip]
        slice_rhs 3 4 => rw [associator_inv_naturality]
        slice_rhs 2 3 => rw [← tensor_id, associator_inv_naturality]
        slice_rhs 1 3 => rw [iso.hom_inv_id_assoc]
        slice_rhs 1 2 => rw [← comp_tensor_id, tensor_id_comp_id_tensor]
        slice_rhs 1 2 => rw [← comp_tensor_id, ← f.mul_hom]
        rw [comp_tensor_id, category.assoc] }
  map M N g :=
    { Hom := g.Hom
      act_hom' := by
        dsimp
        slice_rhs 1 2 => rw [id_tensor_comp_tensor_id, ← tensor_id_comp_id_tensor]
        slice_rhs 2 3 => rw [← g.act_hom]
        rw [category.assoc] }
#align Mod.comap ModCat.comap

-- Lots more could be said about `comap`, e.g. how it interacts with
-- identities, compositions, and equalities of monoid object morphisms.
end ModCat

