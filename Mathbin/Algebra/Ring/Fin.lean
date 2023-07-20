/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Logic.Equiv.Fin
import Mathbin.Algebra.Ring.Equiv
import Mathbin.Algebra.Group.Prod

#align_import algebra.ring.fin from "leanprover-community/mathlib"@"4d392a6c9c4539cbeca399b3ee0afea398fbd2eb"

/-!
# Rings and `fin`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file collects some basic results involving rings and the `fin` type

## Main results

 * `ring_equiv.fin_two`: The product over `fin 2` of some rings is the cartesian product

-/


#print RingEquiv.piFinTwo /-
/-- The product over `fin 2` of some rings is just the cartesian product of these rings. -/
@[simps]
def RingEquiv.piFinTwo (R : Fin 2 → Type _) [∀ i, Semiring (R i)] :
    (∀ i : Fin 2, R i) ≃+* R 0 × R 1 :=
  { piFinTwoEquiv R with
    toFun := piFinTwoEquiv R
    map_add' := fun a b => rfl
    map_mul' := fun a b => rfl }
#align ring_equiv.pi_fin_two RingEquiv.piFinTwo
-/

