/-
Copyright (c) Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
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
  Adjunction.has_colimits_of_shape_of_equivalence e

theorem Equivalence.has_initial_iff (e : C ≌ D) : HasInitial C ↔ HasInitial D :=
  ⟨fun h => has_initial_of_equivalence e.inverse, fun h => has_initial_of_equivalence e.functor⟩

theorem has_terminal_of_equivalence (e : D ⥤ C) [IsEquivalence e] [HasTerminal C] : HasTerminal D :=
  Adjunction.has_limits_of_shape_of_equivalence e

theorem Equivalence.has_terminal_iff (e : C ≌ D) : HasTerminal C ↔ HasTerminal D :=
  ⟨fun h => has_terminal_of_equivalence e.inverse, fun h => has_terminal_of_equivalence e.functor⟩

end CategoryTheory

