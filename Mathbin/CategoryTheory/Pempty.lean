/-
Copyright (c) 2018 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import Mathbin.CategoryTheory.DiscreteCategory

#align_import category_theory.pempty from "leanprover-community/mathlib"@"23aa88e32dcc9d2a24cca7bc23268567ed4cd7d6"

/-!
# The empty category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/


universe w v u

-- morphism levels before object levels. See note [category_theory universes].
namespace CategoryTheory

namespace Functor

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.Functor.emptyEquivalence /-
/-- Equivalence between two empty categories. -/
def emptyEquivalence : Discrete.{w} PEmpty ≌ Discrete.{v} PEmpty :=
  Equivalence.mk
    { obj := PEmpty.elim ∘ Discrete.as
      map := fun x => x.as.elim }
    { obj := PEmpty.elim ∘ Discrete.as
      map := fun x => x.as.elim } (by tidy) (by tidy)
#align category_theory.functor.empty_equivalence CategoryTheory.Functor.emptyEquivalence
-/

#print CategoryTheory.Functor.empty /-
/-- The canonical functor out of the empty category. -/
def empty : Discrete.{w} PEmpty ⥤ C :=
  Discrete.functor PEmpty.elim
#align category_theory.functor.empty CategoryTheory.Functor.empty
-/

variable {C}

#print CategoryTheory.Functor.emptyExt /-
/-- Any two functors out of the empty category are isomorphic. -/
def emptyExt (F G : Discrete.{w} PEmpty ⥤ C) : F ≅ G :=
  Discrete.natIso fun x => x.as.elim
#align category_theory.functor.empty_ext CategoryTheory.Functor.emptyExt
-/

#print CategoryTheory.Functor.uniqueFromEmpty /-
/-- Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def uniqueFromEmpty (F : Discrete.{w} PEmpty ⥤ C) : F ≅ empty C :=
  emptyExt _ _
#align category_theory.functor.unique_from_empty CategoryTheory.Functor.uniqueFromEmpty
-/

#print CategoryTheory.Functor.empty_ext' /-
/-- Any two functors out of the empty category are *equal*. You probably want to use
`empty_ext` instead of this.
-/
theorem empty_ext' (F G : Discrete.{w} PEmpty ⥤ C) : F = G :=
  Functor.ext (fun x => x.as.elim) fun x _ _ => x.as.elim
#align category_theory.functor.empty_ext' CategoryTheory.Functor.empty_ext'
-/

end Functor

end CategoryTheory

