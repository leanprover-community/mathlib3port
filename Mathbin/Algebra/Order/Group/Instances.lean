/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Order.Monoid.OrderDual

#align_import algebra.order.group.instances from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Additional instances for ordered commutative groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


variable {α : Type _}

@[to_additive]
instance [OrderedCommGroup α] : OrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommMonoid, instGroupOrderDual with }

@[to_additive]
instance [LinearOrderedCommGroup α] : LinearOrderedCommGroup αᵒᵈ :=
  { OrderDual.orderedCommGroup, OrderDual.instLinearOrder α with }

