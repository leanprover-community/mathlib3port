import Mathbin.Topology.Sheaves.Presheaf 
import Mathbin.CategoryTheory.Limits.FunctorCategory

/-!
# Presheaves in `C` have limits and colimits when `C` does.
-/


noncomputable theory

universe v u

open CategoryTheory

open CategoryTheory.Limits

variable{C : Type u}[category.{v} C]

namespace Top

instance  [has_limits C] (X : Top) : has_limits (presheaf C X) :=
  by 
    dsimp [presheaf]
    infer_instance

instance  [has_colimits C] (X : Top) : has_colimits (presheaf C X) :=
  by 
    dsimp [presheaf]
    infer_instance

end Top

