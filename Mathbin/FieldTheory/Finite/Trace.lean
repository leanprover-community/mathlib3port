/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll

! This file was ported from Lean 3 source module field_theory.finite.trace
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Trace
import Mathbin.FieldTheory.Finite.GaloisField

/-!
# The trace map for finite fields

We state the fact that the trace map from a finite field of
characteristic `p` to `zmod p` is nondegenerate.

## Tags
finite field, trace
-/


namespace FiniteField

/-- The trace map from a finite field to its prime field is nongedenerate. -/
theorem trace_to_zMod_nondegenerate (F : Type _) [Field F] [Finite F] {a : F} (ha : a ≠ 0) :
    ∃ b : F, Algebra.trace (ZMod (ringChar F)) F (a * b) ≠ 0 :=
  by
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have htr := traceFormNondegenerate (ZMod (ringChar F)) F a
  simp_rw [Algebra.traceForm_apply] at htr
  by_contra' hf
  exact ha (htr hf)
#align finite_field.trace_to_zmod_nondegenerate FiniteField.trace_to_zMod_nondegenerate

end FiniteField

