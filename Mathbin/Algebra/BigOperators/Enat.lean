/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.Enat

/-!
# Big operators in `enat`

A simple lemma about sums in `enat`.
-/


open_locale BigOperators

variable {α : Type _}

namespace Finset

theorem sum_nat_coe_enat (s : Finset α) (f : α → ℕ) : (∑ x in s, (f x : Enat)) = (∑ x in s, f x : ℕ) :=
  (Enat.coeHom.map_sum _ _).symm

end Finset

