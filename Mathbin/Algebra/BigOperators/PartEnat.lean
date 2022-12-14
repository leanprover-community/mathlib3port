/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

! This file was ported from Lean 3 source module algebra.big_operators.part_enat
! leanprover-community/mathlib commit 198161d833f2c01498c39c266b0b3dbe2c7a8c07
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Data.Nat.PartEnat

/-!
# Big operators in `part_enat`

A simple lemma about sums in `part_enat`.
-/


open BigOperators

variable {α : Type _}

namespace Finset

theorem sum_nat_coe_enat (s : Finset α) (f : α → ℕ) :
    (∑ x in s, (f x : PartEnat)) = (∑ x in s, f x : ℕ) :=
  (PartEnat.coeHom.map_sum _ _).symm
#align finset.sum_nat_coe_enat Finset.sum_nat_coe_enat

end Finset

