/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Card
import Algebra.Parity

#align_import data.fintype.parity from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# The cardinality of `fin (bit0 n)` is even.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

namespace Fintype

#print Fintype.IsSquare.decidablePred /-
instance IsSquare.decidablePred [Mul α] [Fintype α] [DecidableEq α] :
    DecidablePred (IsSquare : α → Prop) := fun a => Fintype.decidableExistsFintype
#align fintype.is_square.decidable_pred Fintype.IsSquare.decidablePred
-/

end Fintype

/-- The cardinality of `fin (bit0 n)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
theorem Fintype.card_fin_even {n : ℕ} : Fact (Even (Fintype.card (Fin (bit0 n)))) :=
  ⟨by rw [Fintype.card_fin]; exact even_bit0 _⟩
#align fintype.card_fin_even Fintype.card_fin_even

