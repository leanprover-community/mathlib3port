import Mathbin.CategoryTheory.Limits.Shapes.Kernels
import Mathbin.CategoryTheory.ConcreteCategory.Basic
import Mathbin.Tactic.Elementwise

/-!
# Facts about limits of functors into concrete categories

This file doesn't yet attempt to be exhaustive;
it just contains lemmas that are useful
while comparing categorical limits with existing constructions in concrete categories.
-/


universe u

open CategoryTheory

namespace CategoryTheory.Limits

attribute [elementwise] kernel.condition cokernel.condition

end CategoryTheory.Limits

