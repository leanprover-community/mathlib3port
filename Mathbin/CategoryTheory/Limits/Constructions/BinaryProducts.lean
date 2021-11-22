import Mathbin.CategoryTheory.Limits.Shapes.Terminal 
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks 
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Constructing binary product from pullbacks and terminal object.

If a category has pullbacks and a terminal object, then it has binary products.

TODO: provide the dual result.
-/


universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

/-- Any category with pullbacks and terminal object has binary products. -/
theorem has_binary_products_of_terminal_and_pullbacks (C : Type u) [𝒞 : category.{v} C] [has_terminal C]
  [has_pullbacks C] : has_binary_products C :=
  { HasLimit :=
      fun F =>
        has_limit.mk
          { Cone :=
              { x := pullback (terminal.from (F.obj walking_pair.left)) (terminal.from (F.obj walking_pair.right)),
                π := discrete.nat_trans fun x => walking_pair.cases_on x pullback.fst pullback.snd },
            IsLimit :=
              { lift :=
                  fun c =>
                    pullback.lift (c.π.app walking_pair.left) (c.π.app walking_pair.right) (Subsingleton.elimₓ _ _),
                fac' := fun s c => walking_pair.cases_on c (limit.lift_π _ _) (limit.lift_π _ _),
                uniq' :=
                  fun s m J =>
                    by 
                      rw [←J, ←J]
                      ext <;> rw [limit.lift_π] <;> rfl } } }

