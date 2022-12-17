/-
Copyright (c) Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel

! This file was ported from Lean 3 source module category_theory.limits.shapes.equivalence
! leanprover-community/mathlib commit 706d88f2b8fdfeb0b22796433d7a6c1a010af9f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Adjunction.Limits
import Mathbin.CategoryTheory.Limits.Shapes.Terminal

/-!
# Transporting existence of specific limits across equivalences

For now, we only treat the case of initial and terminal objects, but other special shapes can be
added in the future.
-/


open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

theorem has_initial_of_equivalence (e : D ⥤ C) [IsEquivalence e] [HasInitial C] : HasInitial D :=
  Adjunction.hasColimitsOfShapeOfEquivalence e
#align category_theory.has_initial_of_equivalence CategoryTheory.has_initial_of_equivalence

theorem Equivalence.has_initial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun h => has_initial_of_equivalence e.inverse, fun h => has_initial_of_equivalence e.functor⟩
#align category_theory.equivalence.has_initial_iff CategoryTheory.Equivalence.has_initial_iff

theorem has_terminal_of_equivalence (e : D ⥤ C) [IsEquivalence e] [HasTerminal C] : HasTerminal D :=
  Adjunction.hasLimitsOfShapeOfEquivalence e
#align category_theory.has_terminal_of_equivalence CategoryTheory.has_terminal_of_equivalence

theorem Equivalence.has_terminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun h => has_terminal_of_equivalence e.inverse, fun h => has_terminal_of_equivalence e.functor⟩
#align category_theory.equivalence.has_terminal_iff CategoryTheory.Equivalence.has_terminal_iff

end CategoryTheory

