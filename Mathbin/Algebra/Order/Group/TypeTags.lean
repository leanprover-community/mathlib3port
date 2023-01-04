/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl

! This file was ported from Lean 3 source module algebra.order.group.type_tags
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Order.Group.Instances
import Mathbin.Algebra.Order.Monoid.TypeTags

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

