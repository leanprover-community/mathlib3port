/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Data.Complex.Module
import LinearAlgebra.Orientation

#align_import data.complex.orientation from "leanprover-community/mathlib"@"7d34004e19699895c13c86b78ae62bbaea0bc893"

/-!
# The standard orientation on `ℂ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This had previously been in `linear_algebra.orientation`,
but keeping it separate results in a significant import reduction.
-/


namespace Complex

#print Complex.orientation /-
/-- The standard orientation on `ℂ`. -/
protected noncomputable def orientation : Orientation ℝ ℂ (Fin 2) :=
  Complex.basisOneI.Orientation
#align complex.orientation Complex.orientation
-/

end Complex

