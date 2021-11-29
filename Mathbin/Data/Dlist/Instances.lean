import Mathbin.Control.Traversable.Equiv 
import Mathbin.Control.Traversable.Instances 
import Leanbin.Data.Dlist

/-!
# Traversable instance for dlists

This file provides the equivalence between `list α` and `dlist α` and the traversable instance
for `dlist`.
-/


open Function Equiv

namespace Dlist

variable (α : Type _)

/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def list_equiv_dlist : List α ≃ Dlist α :=
  by 
    refine' { toFun := Dlist.ofList, invFun := Dlist.toList, .. } <;>
      simp [Function.RightInverse, left_inverse, to_list_of_list, of_list_to_list]

instance : Traversable Dlist :=
  Equiv.traversable list_equiv_dlist

instance : IsLawfulTraversable Dlist :=
  Equiv.isLawfulTraversable list_equiv_dlist

instance {α} : Inhabited (Dlist α) :=
  ⟨Dlist.empty⟩

end Dlist

