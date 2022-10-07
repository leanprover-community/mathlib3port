/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Localization.Construction

/-!

# Predicate for localized categories

In this file, a predicate `L.is_localization W` is introduced for a functor `L : C ⥤ D`
and `W : morphism_property C`. It expresses that `L` identifies `D` with the localized
category of `C` with respect to `W` (up to equivalence).

-/


namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D]

variable (L : C ⥤ D) (W : MorphismProperty C)

namespace Functor

/-- The predicate expressing that, up to equivalence, a functor `L : C ⥤ D`
identifies the category `D` with the localized category of `C` with respect
to `W : morphism_property C`. -/
class IsLocalization : Prop where
  inverts : W.IsInvertedBy L
  nonempty_is_equivalence : Nonempty (IsEquivalence (Localization.Construction.lift L inverts))

instance Q_is_localization : W.q.IsLocalization W where
  inverts := W.Q_inverts
  nonempty_is_equivalence := by
    suffices localization.construction.lift W.Q W.Q_inverts = 𝟭 _ by
      apply Nonempty.intro
      rw [this]
      infer_instance
    apply localization.construction.uniq
    simpa only [localization.construction.fac]

end Functor

end CategoryTheory

