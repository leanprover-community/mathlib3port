import Mathbin.Algebra.Group.Defs
import Mathbin.Algebra.Group.ToAdditive

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/


universe u

-- failed to format: format: uncaught backtrack exception
@[ to_additive ]
  instance semigroupPempty : Semigroupₓ Pempty .{ u + 1 } where mul x y := by cases x mul_assoc x y z := by cases x

