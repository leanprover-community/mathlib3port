/-
Copyright (c) 2022 Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémi Bottinelli

! This file was ported from Lean 3 source module category_theory.groupoid.basic
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Groupoid
import Mathbin.Combinatorics.Quiver.Basic

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a few basic properties of groupoids.
-/


namespace CategoryTheory

namespace Groupoid

variable (C : Type _) [Groupoid C]

section Thin

/- warning: category_theory.groupoid.is_thin_iff -> CategoryTheory.Groupoid.isThin_iff is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u1}) [_inst_1 : CategoryTheory.Groupoid.{u2, u1} C], Iff (Quiver.IsThin.{u1, succ u2} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C (CategoryTheory.Groupoid.toCategory.{u2, u1} C _inst_1)))) (forall (c : C), Subsingleton.{succ u2} (Quiver.Hom.{succ u2, u1} C (CategoryTheory.CategoryStruct.toQuiver.{u2, u1} C (CategoryTheory.Category.toCategoryStruct.{u2, u1} C (CategoryTheory.Groupoid.toCategory.{u2, u1} C _inst_1))) c c))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Groupoid.{u1, u2} C], Iff (Quiver.IsThin.{u2, succ u1} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C (CategoryTheory.Groupoid.toCategory.{u1, u2} C _inst_1)))) (forall (c : C), Subsingleton.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C (CategoryTheory.Groupoid.toCategory.{u1, u2} C _inst_1))) c c))
Case conversion may be inaccurate. Consider using '#align category_theory.groupoid.is_thin_iff CategoryTheory.Groupoid.isThin_iffₓ'. -/
theorem isThin_iff : Quiver.IsThin C ↔ ∀ c : C, Subsingleton (c ⟶ c) :=
  by
  refine' ⟨fun h c => h c c, fun h c d => Subsingleton.intro fun f g => _⟩
  haveI := h d
  calc
    f = f ≫ inv g ≫ g := by simp only [inv_eq_inv, is_iso.inv_hom_id, category.comp_id]
    _ = f ≫ inv f ≫ g := by congr
    _ = g := by simp only [inv_eq_inv, is_iso.hom_inv_id_assoc]
    
#align category_theory.groupoid.is_thin_iff CategoryTheory.Groupoid.isThin_iff

end Thin

section Disconnected

#print CategoryTheory.Groupoid.IsTotallyDisconnected /-
/-- A subgroupoid is totally disconnected if it only has loops. -/
def IsTotallyDisconnected :=
  ∀ c d : C, (c ⟶ d) → c = d
#align category_theory.groupoid.is_totally_disconnected CategoryTheory.Groupoid.IsTotallyDisconnected
-/

end Disconnected

end Groupoid

end CategoryTheory

