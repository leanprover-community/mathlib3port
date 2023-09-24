/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Algebra.Order.Group.Instances
import Algebra.Order.Monoid.TypeTags

#align_import algebra.order.group.type_tags from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-! # Ordered group structures on `multiplicative α` and `additive α`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


variable {α : Type _}

instance [OrderedAddCommGroup α] : OrderedCommGroup (Multiplicative α) :=
  { Multiplicative.commGroup, Multiplicative.orderedCommMonoid with }

instance [OrderedCommGroup α] : OrderedAddCommGroup (Additive α) :=
  { Additive.addCommGroup, Additive.orderedAddCommMonoid with }

instance [LinearOrderedAddCommGroup α] : LinearOrderedCommGroup (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommGroup with }

instance [LinearOrderedCommGroup α] : LinearOrderedAddCommGroup (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommGroup with }

