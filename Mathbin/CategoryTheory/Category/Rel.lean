import Mathbin.CategoryTheory.Category.Basic

/-!
The category of types with binary relations as morphisms.
-/


namespace CategoryTheory

universe u

/--  A type synonym for `Type`, which carries the category instance for which
    morphisms are binary relations. -/
def Rel :=
  Type u

instance Rel.inhabited : Inhabited Rel := by
  unfold Rel <;> infer_instance

-- failed to format: format: uncaught backtrack exception
/-- The category of types with binary relations as morphisms. -/
  instance
    rel
    : large_category Rel
    where Hom X Y := X → Y → Prop id X := fun x y => x = y comp X Y Z f g x z := ∃ y , f x y ∧ g y z

end CategoryTheory

