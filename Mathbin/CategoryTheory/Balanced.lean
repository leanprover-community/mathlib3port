/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.balanced
! leanprover-community/mathlib commit 46a64b5b4268c594af770c44d9e502afc6a515cb
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.EpiMono

/-!
# Balanced categories

A category is called balanced if any morphism that is both monic and epic is an isomorphism.

Balanced categories arise frequently. For example, categories in which every monomorphism
(or epimorphism) is strong are balanced. Examples of this are abelian categories and toposes, such
as the category of types.

-/


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

section

variable (C)

/-- A category is called balanced if any morphism that is both monic and epic is an isomorphism. -/
class Balanced : Prop where
  is_iso_of_mono_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f], IsIso f
#align category_theory.balanced CategoryTheory.Balanced

end

theorem is_iso_of_mono_of_epi [Balanced C] {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f :=
  Balanced.is_iso_of_mono_of_epi _
#align category_theory.is_iso_of_mono_of_epi CategoryTheory.is_iso_of_mono_of_epi

theorem is_iso_iff_mono_and_epi [Balanced C] {X Y : C} (f : X ⟶ Y) : IsIso f ↔ Mono f ∧ Epi f :=
  ⟨fun _ => ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ => is_iso_of_mono_of_epi _⟩
#align category_theory.is_iso_iff_mono_and_epi CategoryTheory.is_iso_iff_mono_and_epi

section

attribute [local instance] is_iso_of_mono_of_epi

theorem balanced_opposite [Balanced C] : Balanced Cᵒᵖ :=
  {
    is_iso_of_mono_of_epi := fun X Y f fmono fepi =>
      by
      rw [← Quiver.Hom.op_unop f]
      exact is_iso_of_op _ }
#align category_theory.balanced_opposite CategoryTheory.balanced_opposite

end

end CategoryTheory

