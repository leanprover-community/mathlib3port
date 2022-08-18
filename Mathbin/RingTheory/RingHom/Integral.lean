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

theorem is_integral_stable_under_composition : StableUnderComposition fun R S _ _ f => f.is_integral := by
  introv R hf hg
  exact RingHom.is_integral_trans _ _ hf hg

theorem is_integral_respects_iso : RespectsIso fun R S _ _ f => f.is_integral := by
  apply is_integral_stable_under_composition.respects_iso
  introv x
  skip
  rw [← e.apply_symm_apply x]
  apply RingHom.is_integral_map

theorem is_integral_stable_under_base_change : StableUnderBaseChange fun R S _ _ f => f.is_integral := by
  introv R h x
  skip
  apply TensorProduct.induction_on x
  · apply is_integral_zero
    
  · intro x y
    exact IsIntegral.tmul x (h y)
    
  · intro x y hx hy
    exact is_integral_add _ hx hy
    

end RingHom

