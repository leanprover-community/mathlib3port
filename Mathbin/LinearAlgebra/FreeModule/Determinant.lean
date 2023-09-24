/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Alex J. Best
-/
import LinearAlgebra.Determinant
import LinearAlgebra.FreeModule.Finite.Basic

#align_import linear_algebra.free_module.determinant from "leanprover-community/mathlib"@"fe8d0ff42c3c24d789f491dc2622b6cac3d61564"

/-!
# Determinants in free (finite) modules

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Quite a lot of our results on determinants (that you might know in vector spaces) will work for all
free (finite) modules over any commutative ring.

## Main results

 * `linear_map.det_zero''`: The determinant of the constant zero map is zero, in a finite free
   nontrivial module.
-/


#print LinearMap.det_zero'' /-
@[simp]
theorem LinearMap.det_zero'' {R M : Type _} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] [Nontrivial M] : LinearMap.det (0 : M →ₗ[R] M) = 0 :=
  by
  letI : Nonempty (Module.Free.ChooseBasisIndex R M) := (Module.Free.chooseBasis R M).index_nonempty
  nontriviality R
  exact LinearMap.det_zero' (Module.Free.chooseBasis R M)
#align linear_map.det_zero'' LinearMap.det_zero''
-/

