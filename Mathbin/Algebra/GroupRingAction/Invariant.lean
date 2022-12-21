/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module algebra.group_ring_action.invariant
! leanprover-community/mathlib commit 0743cc5d9d86bcd1bba10f480e948a257d65056f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Subring.Pointwise

/-! # Subrings invariant under an action -/


section Ring

variable (M R : Type _) [Monoid M] [Ring R] [MulSemiringAction M R]

variable (S : Subring R)

open MulAction

variable {R}

/-- A typeclass for subrings invariant under a `mul_semiring_action`. -/
class IsInvariantSubring : Prop where
  smul_mem : ∀ (m : M) {x : R}, x ∈ S → m • x ∈ S
#align is_invariant_subring IsInvariantSubring

instance IsInvariantSubring.toMulSemiringAction [IsInvariantSubring M S] :
    MulSemiringAction M
      S where 
  smul m x := ⟨m • x, IsInvariantSubring.smul_mem m x.2⟩
  one_smul s := Subtype.eq <| one_smul M s
  mul_smul m₁ m₂ s := Subtype.eq <| mul_smul m₁ m₂ s
  smul_add m s₁ s₂ := Subtype.eq <| smul_add m s₁ s₂
  smul_zero m := Subtype.eq <| smul_zero m
  smul_one m := Subtype.eq <| smul_one m
  smul_mul m s₁ s₂ := Subtype.eq <| smul_mul' m s₁ s₂
#align is_invariant_subring.to_mul_semiring_action IsInvariantSubring.toMulSemiringAction

end Ring

