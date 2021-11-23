import Mathbin.Algebra.Group.Defs 
import Mathbin.Algebra.Group.ToAdditive

/-!
# Instances on pempty

This file collects facts about algebraic structures on the (universe-polymorphic) empty type, e.g.
that it is a semigroup.
-/


universe u

@[toAdditive]
instance semigroupPempty : Semigroupₓ Pempty.{u + 1} :=
  { mul :=
      fun x y =>
        by 
          cases x,
    mul_assoc :=
      fun x y z =>
        by 
          cases x }

