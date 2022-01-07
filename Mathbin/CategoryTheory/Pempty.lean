import Mathbin.CategoryTheory.DiscreteCategory

/-!
# The empty category

Defines a category structure on `pempty`, and the unique functor `pempty ⥤ C` for any category `C`.
-/


universe w v u

namespace CategoryTheory

namespace Functor

variable (C : Type u) [category.{v} C]

/-- Equivalence between two empty categories. -/
def empty_equivalence : discrete.{w} Pempty ≌ discrete.{v} Pempty :=
  equivalence.mk { obj := Pempty.elimₓ, map := fun x => x.elim } { obj := Pempty.elimₓ, map := fun x => x.elim }
    (by
      tidy)
    (by
      tidy)

/-- The canonical functor out of the empty category. -/
def Empty : discrete.{w} Pempty ⥤ C :=
  discrete.functor Pempty.elimₓ

variable {C}

/-- Any two functors out of the empty category are isomorphic. -/
def empty_ext (F G : discrete.{w} Pempty ⥤ C) : F ≅ G :=
  discrete.nat_iso fun x => Pempty.elimₓ x

/-- Any functor out of the empty category is isomorphic to the canonical functor from the empty
category.
-/
def unique_from_empty (F : discrete.{w} Pempty ⥤ C) : F ≅ Empty C :=
  empty_ext _ _

/-- Any two functors out of the empty category are *equal*. You probably want to use
`empty_ext` instead of this.
-/
theorem empty_ext' (F G : discrete.{w} Pempty ⥤ C) : F = G :=
  Functor.ext (fun x => x.elim) fun x _ _ => x.elim

end Functor

end CategoryTheory

