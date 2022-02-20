/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.SetTheory.Cardinal

/-!
# Finite Cardinality Functions

## Main Definitions

* `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`.
* `enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `enat.card α = ⊤`.

-/


open Cardinal

noncomputable section

variable {α : Type _}

namespace Nat

/-- `nat.card α` is the cardinality of `α` as a natural number.
  If `α` is infinite, `nat.card α = 0`. -/
protected def card (α : Type _) : ℕ :=
  (mk α).toNat

@[simp]
theorem card_eq_fintype_card [Fintype α] : Nat.card α = Fintype.card α :=
  mk_to_nat_eq_card

@[simp]
theorem card_eq_zero_of_infinite [Infinite α] : Nat.card α = 0 :=
  mk_to_nat_of_infinite

end Nat

namespace Enat

/-- `enat.card α` is the cardinality of `α` as an extended natural number.
  If `α` is infinite, `enat.card α = ⊤`. -/
def card (α : Type _) : Enat :=
  (mk α).toEnat

@[simp]
theorem card_eq_coe_fintype_card [Fintype α] : card α = Fintype.card α :=
  mk_to_enat_eq_coe_card

@[simp]
theorem card_eq_top_of_infinite [Infinite α] : card α = ⊤ :=
  mk_to_enat_of_infinite

end Enat

