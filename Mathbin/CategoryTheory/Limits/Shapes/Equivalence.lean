/-
Copyright (c) Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.shapes.equivalence
! leanprover-community/mathlib commit f47581155c818e6361af4e4fda60d27d020c226b
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transporting existence of specific limits across equivalences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

#print CategoryTheory.hasInitial_of_equivalence /-
theorem hasInitial_of_equivalence (e : D ⥤ C) [IsEquivalence e] [HasInitial C] : HasInitial D :=
  Adjunction.hasColimitsOfShape_of_equivalence e
#align category_theory.has_initial_of_equivalence CategoryTheory.hasInitial_of_equivalence
-/

/- warning: category_theory.equivalence.has_initial_iff -> CategoryTheory.Equivalence.hasInitial_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D], (CategoryTheory.Equivalence.{u1, u2, u3, u4} C _inst_1 D _inst_2) -> (Iff (CategoryTheory.Limits.HasInitial.{u1, u3} C _inst_1) (CategoryTheory.Limits.HasInitial.{u2, u4} D _inst_2))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D], (CategoryTheory.Equivalence.{u1, u2, u3, u4} C D _inst_1 _inst_2) -> (Iff (CategoryTheory.Limits.HasInitial.{u1, u3} C _inst_1) (CategoryTheory.Limits.HasInitial.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.has_initial_iff CategoryTheory.Equivalence.hasInitial_iffₓ'. -/
theorem Equivalence.hasInitial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun h => has_initial_of_equivalence e.inverse, fun h => has_initial_of_equivalence e.functor⟩
#align category_theory.equivalence.has_initial_iff CategoryTheory.Equivalence.hasInitial_iff

#print CategoryTheory.hasTerminal_of_equivalence /-
theorem hasTerminal_of_equivalence (e : D ⥤ C) [IsEquivalence e] [HasTerminal C] : HasTerminal D :=
  Adjunction.hasLimitsOfShape_of_equivalence e
#align category_theory.has_terminal_of_equivalence CategoryTheory.hasTerminal_of_equivalence
-/

/- warning: category_theory.equivalence.has_terminal_iff -> CategoryTheory.Equivalence.hasTerminal_iff is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D], (CategoryTheory.Equivalence.{u1, u2, u3, u4} C _inst_1 D _inst_2) -> (Iff (CategoryTheory.Limits.HasTerminal.{u1, u3} C _inst_1) (CategoryTheory.Limits.HasTerminal.{u2, u4} D _inst_2))
but is expected to have type
  forall {C : Type.{u3}} [_inst_1 : CategoryTheory.Category.{u1, u3} C] {D : Type.{u4}} [_inst_2 : CategoryTheory.Category.{u2, u4} D], (CategoryTheory.Equivalence.{u1, u2, u3, u4} C D _inst_1 _inst_2) -> (Iff (CategoryTheory.Limits.HasTerminal.{u1, u3} C _inst_1) (CategoryTheory.Limits.HasTerminal.{u2, u4} D _inst_2))
Case conversion may be inaccurate. Consider using '#align category_theory.equivalence.has_terminal_iff CategoryTheory.Equivalence.hasTerminal_iffₓ'. -/
theorem Equivalence.hasTerminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun h => has_terminal_of_equivalence e.inverse, fun h => has_terminal_of_equivalence e.functor⟩
#align category_theory.equivalence.has_terminal_iff CategoryTheory.Equivalence.hasTerminal_iff

end CategoryTheory

