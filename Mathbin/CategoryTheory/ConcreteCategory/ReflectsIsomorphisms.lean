import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.CategoryTheory.ReflectsIsomorphisms

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/


universe u

namespace CategoryTheory

-- failed to format: format: uncaught backtrack exception
instance : reflects_isomorphisms ( forget ( Type u ) ) where reflects X Y f i := i

variable (C : Type (u + 1)) [category C] [concrete_category.{u} C]

variable (D : Type (u + 1)) [category D] [concrete_category.{u} D]

/-- 
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
theorem reflects_isomorphisms_forget₂ [has_forget₂ C D] [reflects_isomorphisms (forget C)] :
    reflects_isomorphisms (forget₂ C D) :=
  { reflects := fun X Y f i => by
      skip
      have i' : is_iso ((forget D).map ((forget₂ C D).map f)) := functor.map_is_iso (forget D) _
      have : is_iso ((forget C).map f) := by
        have := has_forget₂.forget_comp
        dsimp  at this
        rw [← this]
        exact i'
      apply is_iso_of_reflects_iso f (forget C) }

end CategoryTheory

