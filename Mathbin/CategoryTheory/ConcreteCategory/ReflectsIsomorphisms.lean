import Mathbin.CategoryTheory.ConcreteCategory.Basic 
import Mathbin.CategoryTheory.ReflectsIsomorphisms

/-!
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
whose forgetful functors both reflect isomorphisms, itself reflects isomorphisms.
-/


universe u

namespace CategoryTheory

instance : reflects_isomorphisms (forget (Type u)) :=
  { reflects := fun X Y f i => i }

variable (C : Type (u + 1)) [category C] [concrete_category.{u} C]

variable (D : Type (u + 1)) [category D] [concrete_category.{u} D]

-- error in CategoryTheory.ConcreteCategory.ReflectsIsomorphisms: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
A `forget₂ C D` forgetful functor between concrete categories `C` and `D`
where `forget C` reflects isomorphisms, itself reflects isomorphisms.
-/
theorem reflects_isomorphisms_forget₂
[has_forget₂ C D]
[reflects_isomorphisms (forget C)] : reflects_isomorphisms (forget₂ C D) :=
{ reflects := λ X Y f i, begin
    resetI,
    haveI [ident i'] [":", expr is_iso ((forget D).map ((forget₂ C D).map f))] [":=", expr functor.map_is_iso (forget D) _],
    haveI [] [":", expr is_iso ((forget C).map f)] [":=", expr begin
       have [] [] [":=", expr has_forget₂.forget_comp],
       dsimp [] [] [] ["at", ident this],
       rw ["<-", expr this] [],
       exact [expr i']
     end],
    apply [expr is_iso_of_reflects_iso f (forget C)]
  end }

end CategoryTheory

