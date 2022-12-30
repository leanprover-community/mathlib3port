/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module data.matrix.char_p
! leanprover-community/mathlib commit 09597669f02422ed388036273d8848119699c22f
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Algebra.CharP.Basic

/-!
# Matrices in prime characteristic
-/


open Matrix

variable {n : Type _} [Fintype n] {R : Type _} [Ring R]

instance Matrix.char_p [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] : CharP (Matrix n n R) p :=
  ⟨by
    intro k
    rw [← CharP.cast_eq_zero_iff R p k, ← Nat.cast_zero, ← map_nat_cast <| scalar n]
    convert scalar_inj; · simp; · assumption⟩
#align matrix.char_p Matrix.char_p

