/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser

! This file was ported from Lean 3 source module number_theory.zsqrtd.to_real
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Real.Sqrt
import Mathbin.NumberTheory.Zsqrtd.Basic

/-!
# Image of `zsqrtd` in `ℝ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `zsqrtd.to_real` and related lemmas.
It is in a separate file to avoid pulling in all of `data.real` into `data.zsqrtd`.
-/


namespace Zsqrtd

#print Zsqrtd.toReal /-
/-- The image of `zsqrtd` in `ℝ`, using `real.sqrt` which takes the positive root of `d`.

If the negative root is desired, use `to_real h a.conj`. -/
@[simps]
noncomputable def toReal {d : ℤ} (h : 0 ≤ d) : ℤ√d →+* ℝ :=
  lift ⟨Real.sqrt d, Real.mul_self_sqrt (Int.cast_nonneg.mpr h)⟩
#align zsqrtd.to_real Zsqrtd.toReal
-/

theorem toReal_injective {d : ℤ} (h0d : 0 ≤ d) (hd : ∀ n : ℤ, d ≠ n * n) :
    Function.Injective (toReal h0d) :=
  lift_injective _ hd
#align zsqrtd.to_real_injective Zsqrtd.toReal_injective

end Zsqrtd

