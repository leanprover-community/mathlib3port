/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis, Leonardo de Moura, Mario Carneiro, Floris van Doorn
-/
import Mathbin.Algebra.Field.Basic
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.GroupPower.Order
import Mathbin.Algebra.Order.Ring
import Mathbin.Order.Bounds
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Linear ordered (semi)fields

A linear ordered (semi)field is a (semi)field equipped with a linear order such that
* addition respects the order: `a ≤ b → c + a ≤ c + b`;
* multiplication of positives is positive: `0 < a → 0 < b → 0 < a * b`;
* `0 < 1`.

## Main Definitions

* `linear_ordered_semifield`: Typeclass for linear order semifields.
* `linear_ordered_field`: Typeclass for linear ordered fields.

## Implementation details

For olean caching reasons, this file is separate to the main file, algebra.order.field.
The lemmata are instead located there.

-/


/-- A linear ordered semifield is a field with a linear order respecting the operations. -/
@[protect_proj]
class LinearOrderedSemifield (α : Type _) extends LinearOrderedSemiring α, Semifield α

/-- A linear ordered field is a field with a linear order respecting the operations. -/
@[protect_proj]
class LinearOrderedField (α : Type _) extends LinearOrderedCommRing α, Field α

-- See note [lower instance priority]
instance (priority := 100) LinearOrderedField.toLinearOrderedSemifield {α} [LinearOrderedField α] :
    LinearOrderedSemifield α :=
  { LinearOrderedRing.toLinearOrderedSemiring, ‹LinearOrderedField α› with }

