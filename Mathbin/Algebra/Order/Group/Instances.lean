/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.instances
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Defs
import Mathbin.Algebra.Order.Monoid.OrderDual

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
  { OrderDual.orderedCommGroup, OrderDual.linearOrder α with }

