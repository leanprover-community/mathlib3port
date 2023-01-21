/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.parity
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Algebra.Parity

/-!
# The cardinality of `fin (bit0 n)` is even.
-/


variable {α : Type _}

namespace Fintype

#print Fintype.IsSquare.decidablePred /-
instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α → Prop) := fun a => Fintype.decidableExistsFintype
#align fintype.is_square.decidable_pred Fintype.IsSquare.decidablePred
-/

end Fintype

#print Fintype.card_fin_even /-
/-- The cardinality of `fin (bit0 n)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
theorem Fintype.card_fin_even {n : ℕ} : Fact (Even (Fintype.card (Fin (bit0 n)))) :=
  ⟨by
    rw [Fintype.card_fin]
    exact even_bit0 _⟩
#align fintype.card_fin_even Fintype.card_fin_even
-/

