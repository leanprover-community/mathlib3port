/-
Copyright (c) 2018 Michael Jendrusch. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jendrusch, Scott Morrison

! This file was ported from Lean 3 source module category_theory.monoidal.types.basic
! leanprover-community/mathlib commit 95a87616d63b3cb49d3fe678d416fbe9c4217bf4
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Monoidal.Functor
import Mathbin.CategoryTheory.Monoidal.OfChosenFiniteProducts.Basic
import Mathbin.CategoryTheory.Limits.Shapes.Types
import Mathbin.Logic.Equiv.Fin

/-!
# The category of types is a monoidal category
-/


open CategoryTheory

open CategoryTheory.Limits

open Tactic

universe v u

namespace CategoryTheory

#print CategoryTheory.typesMonoidal /-
instance typesMonoidal : MonoidalCategory.{u} (Type u) :=
  monoidalOfChosenFiniteProducts Types.terminalLimitCone Types.binaryProductLimitCone
#align category_theory.types_monoidal CategoryTheory.typesMonoidal
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.tensor_apply /-
@[simp]
theorem tensor_apply {W X Y Z : Type u} (f : W ⟶ X) (g : Y ⟶ Z) (p : W ⊗ Y) :
    (f ⊗ g) p = (f p.1, g p.2) :=
  rfl
#align category_theory.tensor_apply CategoryTheory.tensor_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.leftUnitor_hom_apply /-
@[simp]
theorem leftUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    ((λ_ X).Hom : 𝟙_ (Type u) ⊗ X → X) (p, x) = x :=
  rfl
#align category_theory.left_unitor_hom_apply CategoryTheory.leftUnitor_hom_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.leftUnitor_inv_apply /-
@[simp]
theorem leftUnitor_inv_apply {X : Type u} {x : X} :
    ((λ_ X).inv : X ⟶ 𝟙_ (Type u) ⊗ X) x = (PUnit.unit, x) :=
  rfl
#align category_theory.left_unitor_inv_apply CategoryTheory.leftUnitor_inv_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.rightUnitor_hom_apply /-
@[simp]
theorem rightUnitor_hom_apply {X : Type u} {x : X} {p : PUnit} :
    ((ρ_ X).Hom : X ⊗ 𝟙_ (Type u) → X) (x, p) = x :=
  rfl
#align category_theory.right_unitor_hom_apply CategoryTheory.rightUnitor_hom_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.rightUnitor_inv_apply /-
@[simp]
theorem rightUnitor_inv_apply {X : Type u} {x : X} :
    ((ρ_ X).inv : X ⟶ X ⊗ 𝟙_ (Type u)) x = (x, PUnit.unit) :=
  rfl
#align category_theory.right_unitor_inv_apply CategoryTheory.rightUnitor_inv_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.associator_hom_apply /-
@[simp]
theorem associator_hom_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    ((α_ X Y Z).Hom : (X ⊗ Y) ⊗ Z → X ⊗ Y ⊗ Z) ((x, y), z) = (x, (y, z)) :=
  rfl
#align category_theory.associator_hom_apply CategoryTheory.associator_hom_apply
-/

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
#print CategoryTheory.associator_inv_apply /-
@[simp]
theorem associator_inv_apply {X Y Z : Type u} {x : X} {y : Y} {z : Z} :
    ((α_ X Y Z).inv : X ⊗ Y ⊗ Z → (X ⊗ Y) ⊗ Z) (x, (y, z)) = ((x, y), z) :=
  rfl
#align category_theory.associator_inv_apply CategoryTheory.associator_inv_apply
-/

/- warning: category_theory.monoidal_functor.map_pi -> CategoryTheory.MonoidalFunctor.mapPi is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] (F : CategoryTheory.MonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2) (n : Nat) (β : Type.{u3}), CategoryTheory.Iso.{u2, u1} C _inst_1 (CategoryTheory.Functor.obj.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F)) ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> β)) (CategoryTheory.MonoidalCategory.tensorObj.{u2, u1} C _inst_1 _inst_2 (CategoryTheory.Functor.obj.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F)) β) (CategoryTheory.Functor.obj.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F)) ((Fin n) -> β)))
but is expected to have type
  forall {C : Type.{u1}} [_inst_1 : CategoryTheory.Category.{u2, u1} C] [_inst_2 : CategoryTheory.MonoidalCategory.{u2, u1} C _inst_1] (F : CategoryTheory.MonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2) (n : Nat) (β : Type.{u3}), CategoryTheory.Iso.{u2, u1} C _inst_1 (Prefunctor.obj.{succ u3, succ u2, succ u3, u1} Type.{u3} (CategoryTheory.CategoryStruct.toQuiver.{u3, succ u3} Type.{u3} (CategoryTheory.Category.toCategoryStruct.{u3, succ u3} Type.{u3} CategoryTheory.types.{u3})) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F))) ((Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> β)) (CategoryTheory.MonoidalCategory.tensorObj.{u2, u1} C _inst_1 _inst_2 (Prefunctor.obj.{succ u3, succ u2, succ u3, u1} Type.{u3} (CategoryTheory.CategoryStruct.toQuiver.{u3, succ u3} Type.{u3} (CategoryTheory.Category.toCategoryStruct.{u3, succ u3} Type.{u3} CategoryTheory.types.{u3})) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F))) β) (Prefunctor.obj.{succ u3, succ u2, succ u3, u1} Type.{u3} (CategoryTheory.CategoryStruct.toQuiver.{u3, succ u3} Type.{u3} (CategoryTheory.Category.toCategoryStruct.{u3, succ u3} Type.{u3} CategoryTheory.types.{u3})) C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} C _inst_1 (CategoryTheory.LaxMonoidalFunctor.toFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 (CategoryTheory.MonoidalFunctor.toLaxMonoidalFunctor.{u3, u2, succ u3, u1} Type.{u3} CategoryTheory.types.{u3} CategoryTheory.typesMonoidal.{u3} C _inst_1 _inst_2 F))) ((Fin n) -> β)))
Case conversion may be inaccurate. Consider using '#align category_theory.monoidal_functor.map_pi CategoryTheory.MonoidalFunctor.mapPiₓ'. -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
-- We don't yet have an API for tensor products indexed by finite ordered types,
-- but it would be nice to state how monoidal functors preserve these.
/-- If `F` is a monoidal functor out of `Type`, it takes the (n+1)st cartesian power
of a type to the image of that type, tensored with the image of the nth cartesian power. -/
noncomputable def MonoidalFunctor.mapPi {C : Type _} [Category C] [MonoidalCategory C]
    (F : MonoidalFunctor (Type _) C) (n : ℕ) (β : Type _) :
    F.obj (Fin (n + 1) → β) ≅ F.obj β ⊗ F.obj (Fin n → β) :=
  Functor.mapIso _ (Equiv.piFinSucc n β).toIso ≪≫ (asIso (F.μ β (Fin n → β))).symm
#align category_theory.monoidal_functor.map_pi CategoryTheory.MonoidalFunctor.mapPi

end CategoryTheory

