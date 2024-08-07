/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Algebra.Group.Prod
import Algebra.Order.Monoid.Cancel.Defs
import Algebra.Order.Monoid.Unbundled.ExistsOfLE

#align_import algebra.order.monoid.prod from "leanprover-community/mathlib"@"448144f7ae193a8990cb7473c9e9a01990f64ac7"

/-! # Products of ordered monoids

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


namespace Prod

variable {α β M N : Type _}

@[to_additive]
instance [OrderedCommMonoid α] [OrderedCommMonoid β] : OrderedCommMonoid (α × β) :=
  { Prod.commMonoid, Prod.partialOrder _ _ with
    mul_le_mul_left := fun a b h c => ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩ }

@[to_additive]
instance [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] :
    OrderedCancelCommMonoid (M × N) :=
  { Prod.orderedCommMonoid with
    le_of_mul_le_mul_left := fun a b c h =>
      ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
instance [LE α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
    ExistsMulOfLE (α × β) :=
  ⟨fun a b h =>
    let ⟨c, hc⟩ := exists_hMul_of_le h.1
    let ⟨d, hd⟩ := exists_hMul_of_le h.2
    ⟨(c, d), ext hc hd⟩⟩

@[to_additive]
instance [CanonicallyOrderedAddCommMonoid α] [CanonicallyOrderedAddCommMonoid β] :
    CanonicallyOrderedAddCommMonoid (α × β) :=
  { Prod.orderedCommMonoid, Prod.orderBot _ _, Prod.existsMulOfLE with
    le_self_mul := fun a b => ⟨le_self_mul, le_self_mul⟩ }

end Prod

