/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import Mathbin.Algebra.Squarefree
import Mathbin.Data.Zmod.Basic
import Mathbin.RingTheory.Int.Basic

#align_import ring_theory.zmod from "leanprover-community/mathlib"@"d64d67d000b974f0d86a2be7918cf800be6271c8"

/-!
# Ring theoretic facts about `zmod n`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We collect a few facts about `zmod n` that need some ring theory to be proved/stated

## Main statements

* `is_reduced_zmod` - `zmod n` is reduced for all squarefree `n`.
-/


#print isReduced_zmod /-
@[simp]
theorem isReduced_zmod {n : ℕ} : IsReduced (ZMod n) ↔ Squarefree n ∨ n = 0 := by
  rw [←
    RingHom.ker_isRadical_iff_reduced_of_surjective
      (ZMod.ringHom_surjective <| Int.castRingHom <| ZMod n),
    ZMod.ker_int_castRingHom, ← isRadical_iff_span_singleton, isRadical_iff_squarefree_or_zero,
    Int.squarefree_coe_nat, Nat.cast_eq_zero]
#align is_reduced_zmod isReduced_zmod
-/

instance {n : ℕ} [Fact <| Squarefree n] : IsReduced (ZMod n) :=
  isReduced_zmod.2 <| Or.inl <| Fact.out _

