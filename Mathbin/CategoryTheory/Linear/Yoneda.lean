import Mathbin.Algebra.Category.Module.Basic 
import Mathbin.CategoryTheory.Linear.Default 
import Mathbin.CategoryTheory.Preadditive.AdditiveFunctor 
import Mathbin.CategoryTheory.Preadditive.Opposite

/-!
# The Yoneda embedding for `R`-linear categories

The Yoneda embedding for `R`-linear categories `C`,
sends an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`.

TODO: `linear_yoneda R C` is `R`-linear.
TODO: In fact, `linear_yoneda` itself is additive and `R`-linear.
-/


open Opposite

namespace CategoryTheory

variable (R : Type _) [Ringₓ R] (C : Type _) [category C] [preadditive C] [linear R C]

/-- The Yoneda embedding for `R`-linear categories `C`,
sending an object `X : C` to the `Module R`-valued presheaf on `C`,
with value on `Y : Cᵒᵖ` given by `Module.of R (unop Y ⟶ X)`. -/
@[simps]
def linear_yoneda : C ⥤ Cᵒᵖ ⥤ ModuleCat R :=
  { obj :=
      fun X =>
        { obj := fun Y => ModuleCat.of R (unop Y ⟶ X), map := fun Y Y' f => linear.left_comp R _ f.unop,
          map_comp' :=
            fun _ _ _ f g =>
              by 
                ext 
                dsimp 
                erw [category.assoc],
          map_id' :=
            fun Y =>
              by 
                ext 
                dsimp 
                erw [category.id_comp] },
    map := fun X X' f => { app := fun Y => linear.right_comp R _ f } }

instance linear_yoneda_obj_additive (X : C) : ((linear_yoneda R C).obj X).Additive :=
  {  }

end CategoryTheory

