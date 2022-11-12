/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Order.Group.Instances
import Mathbin.Algebra.Order.Monoid.TypeTags

/-! # Ordered group structures on `multiplicative α` and `additive α`. -/


variable {α : Type _}

instance [OrderedAddCommGroup α] : OrderedCommGroup (Multiplicative α) :=
  { Multiplicative.commGroup, Multiplicative.orderedCommMonoid with }

instance [OrderedCommGroup α] : OrderedAddCommGroup (Additive α) :=
  { Additive.addCommGroup, Additive.orderedAddCommMonoid with }

instance [LinearOrderedAddCommGroup α] : LinearOrderedCommGroup (Multiplicative α) :=
  { Multiplicative.linearOrder, Multiplicative.orderedCommGroup with }

instance [LinearOrderedCommGroup α] : LinearOrderedAddCommGroup (Additive α) :=
  { Additive.linearOrder, Additive.orderedAddCommGroup with }

