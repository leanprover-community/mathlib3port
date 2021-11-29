import Mathbin.Algebra.Category.Group.Basic 
import Mathbin.CategoryTheory.Preadditive.Default

/-!
# The category of additive commutative groups is preadditive.
-/


open CategoryTheory

universe u

namespace AddCommGroupₓₓ

instance : preadditive AddCommGroupₓₓ :=
  { add_comp' :=
      fun P Q R f f' g =>
        show (f+f') ≫ g = (f ≫ g)+f' ≫ g by 
          ext 
          simp ,
    comp_add' :=
      fun P Q R f g g' =>
        show (f ≫ g+g') = (f ≫ g)+f ≫ g' by 
          ext 
          simp  }

end AddCommGroupₓₓ

