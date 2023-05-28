/-
Copyright (c) 2021 Chris Hughes, Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Junyan Xu

! This file was ported from Lean 3 source module data.polynomial.cardinal
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Basic
import Mathbin.SetTheory.Cardinal.Ordinal

/-!
# Cardinality of Polynomial Ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The reuslt in this file is that the cardinality of `R[X]` is at most the maximum
of `#R` and `ℵ₀`.
-/


universe u

open scoped Cardinal Polynomial

open Cardinal

namespace Polynomial

@[simp]
theorem cardinal_mk_eq_max {R : Type u} [Semiring R] [Nontrivial R] : (#R[X]) = max (#R) ℵ₀ :=
  (toFinsuppIso R).toEquiv.cardinal_eq.trans <| by
    rw [AddMonoidAlgebra, mk_finsupp_lift_of_infinite, lift_uzero, max_comm]; rfl
#align polynomial.cardinal_mk_eq_max Polynomial.cardinal_mk_eq_max

theorem cardinal_mk_le_max {R : Type u} [Semiring R] : (#R[X]) ≤ max (#R) ℵ₀ :=
  by
  cases subsingleton_or_nontrivial R
  · exact (mk_eq_one _).trans_le (le_max_of_le_right one_le_aleph_0)
  · exact cardinal_mk_eq_max.le
#align polynomial.cardinal_mk_le_max Polynomial.cardinal_mk_le_max

end Polynomial

