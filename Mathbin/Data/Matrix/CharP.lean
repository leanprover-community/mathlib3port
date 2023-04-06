/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson

! This file was ported from Lean 3 source module data.matrix.char_p
! leanprover-community/mathlib commit d64d67d000b974f0d86a2be7918cf800be6271c8
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Matrix.Basic
import Mathbin.Algebra.CharP.Basic

/-!
# Matrices in prime characteristic

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Matrix

variable {n : Type _} [Fintype n] {R : Type _} [Ring R]

/- warning: matrix.char_p -> Matrix.charP is a dubious translation:
lean 3 declaration is
  forall {n : Type.{u1}} [_inst_1 : Fintype.{u1} n] {R : Type.{u2}} [_inst_2 : Ring.{u2} R] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Nonempty.{succ u1} n] (p : Nat) [_inst_5 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (AddCommGroupWithOne.toAddGroupWithOne.{u2} R (Ring.toAddCommGroupWithOne.{u2} R _inst_2))) p], CharP.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (AddGroupWithOne.toAddMonoidWithOne.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (AddCommGroupWithOne.toAddGroupWithOne.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toAddCommGroupWithOne.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.ring.{u2, u1} n R _inst_1 (fun (a : n) (b : n) => _inst_3 a b) _inst_2)))) p
but is expected to have type
  forall {n : Type.{u1}} [_inst_1 : Fintype.{u1} n] {R : Type.{u2}} [_inst_2 : Ring.{u2} R] [_inst_3 : DecidableEq.{succ u1} n] [_inst_4 : Nonempty.{succ u1} n] (p : Nat) [_inst_5 : CharP.{u2} R (AddGroupWithOne.toAddMonoidWithOne.{u2} R (Ring.toAddGroupWithOne.{u2} R _inst_2)) p], CharP.{max u2 u1} (Matrix.{u1, u1, u2} n n R) (AddGroupWithOne.toAddMonoidWithOne.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Ring.toAddGroupWithOne.{max u1 u2} (Matrix.{u1, u1, u2} n n R) (Matrix.instRingMatrix.{u2, u1} n R _inst_1 (fun (a : n) (b : n) => _inst_3 a b) _inst_2))) p
Case conversion may be inaccurate. Consider using '#align matrix.char_p Matrix.charPₓ'. -/
instance Matrix.charP [DecidableEq n] [Nonempty n] (p : ℕ) [CharP R p] : CharP (Matrix n n R) p :=
  ⟨by
    intro k
    rw [← CharP.cast_eq_zero_iff R p k, ← Nat.cast_zero, ← map_natCast <| scalar n]
    convert scalar_inj; · simp; · assumption⟩
#align matrix.char_p Matrix.charP

