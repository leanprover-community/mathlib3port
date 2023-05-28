/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module data.complex.orientation
! leanprover-community/mathlib commit 7d34004e19699895c13c86b78ae62bbaea0bc893
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Complex.Module
import Mathbin.LinearAlgebra.Orientation

/-!
# The standard orientation on `ℂ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This had previously been in `linear_algebra.orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.Orientation
#align complex.orientation Complex.orientation

end Complex

