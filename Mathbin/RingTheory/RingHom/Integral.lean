/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.LocalProperties
import Mathbin.RingTheory.Localization.Integral

/-!

# The meta properties of integral ring homomorphisms.

-/


namespace RingHom

open TensorProduct

open TensorProduct Algebra.TensorProduct

theorem isIntegralStableUnderComposition : StableUnderComposition fun R S _ _ f => f.is_integral := by
  introv R hf hg
  exact RingHom.isIntegralTrans _ _ hf hg
#align ring_hom.is_integral_stable_under_composition RingHom.isIntegralStableUnderComposition

theorem isIntegralRespectsIso : RespectsIso fun R S _ _ f => f.is_integral := by
  apply is_integral_stable_under_composition.respects_iso
  introv x
  skip
  rw [← e.apply_symm_apply x]
  apply RingHom.isIntegralMap
#align ring_hom.is_integral_respects_iso RingHom.isIntegralRespectsIso

theorem isIntegralStableUnderBaseChange : StableUnderBaseChange fun R S _ _ f => f.is_integral := by
  introv R h x
  skip
  apply TensorProduct.induction_on x
  · apply isIntegralZero
    
  · intro x y
    exact IsIntegral.tmul x (h y)
    
  · intro x y hx hy
    exact isIntegralAdd _ hx hy
    
#align ring_hom.is_integral_stable_under_base_change RingHom.isIntegralStableUnderBaseChange

end RingHom

