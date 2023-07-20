/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Instances
import Mathbin.Algebra.Order.Monoid.Prod

#align_import algebra.order.group.prod from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-!
# Products of ordered commutative groups.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Prod

variable {G H : Type _}

@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.commGroup, Prod.partialOrder G H, Prod.orderedCancelCommMonoid with }

end Prod

