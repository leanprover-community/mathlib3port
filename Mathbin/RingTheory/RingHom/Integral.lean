/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import RingTheory.RingHomProperties
import RingTheory.IntegralClosure.IsIntegral.Defs

#align_import ring_theory.ring_hom.integral from "leanprover-community/mathlib"@"d07a9c875ed7139abfde6a333b2be205c5bd404e"

/-!

# The meta properties of integral ring homomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

#print RingHom.isIntegral_stableUnderComposition /-
theorem isIntegral_stableUnderComposition : StableUnderComposition fun R S _ _ f => f.is_integral :=
  by introv R hf hg; exact RingHom.IsIntegral.trans _ _ hf hg
#align ring_hom.is_integral_stable_under_composition RingHom.isIntegral_stableUnderComposition
-/

#print RingHom.isIntegral_respectsIso /-
theorem isIntegral_respectsIso : RespectsIso fun R S _ _ f => f.is_integral :=
  by
  apply is_integral_stable_under_composition.respects_iso
  introv x
  skip
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralElem_map
#align ring_hom.is_integral_respects_iso RingHom.isIntegral_respectsIso
-/

#print RingHom.isIntegral_stableUnderBaseChange /-
theorem isIntegral_stableUnderBaseChange : StableUnderBaseChange fun R S _ _ f => f.is_integral :=
  by
  refine' stable_under_base_change.mk _ is_integral_respects_iso _
  introv h x
  skip
  apply TensorProduct.induction_on x
  · apply isIntegral_zero
  · intro x y; exact IsIntegral.tmul x (h y)
  · intro x y hx hy; exact IsIntegral.add _ hx hy
#align ring_hom.is_integral_stable_under_base_change RingHom.isIntegral_stableUnderBaseChange
-/

end RingHom

