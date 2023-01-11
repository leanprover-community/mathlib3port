/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module ring_theory.ring_hom.integral
! leanprover-community/mathlib commit ccad6d5093bd2f5c6ca621fc74674cce51355af6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.RingHomProperties

/-!

# The meta properties of integral ring homomorphisms.

-/


namespace RingHom

open TensorProduct

open TensorProduct Algebra.TensorProduct

theorem is_integral_stable_under_composition :
    StableUnderComposition fun R S _ _ f => f.is_integral :=
  by
  introv R hf hg
  exact RingHom.is_integral_trans _ _ hf hg
#align ring_hom.is_integral_stable_under_composition RingHom.is_integral_stable_under_composition

theorem is_integral_respects_iso : RespectsIso fun R S _ _ f => f.is_integral :=
  by
  apply is_integral_stable_under_composition.respects_iso
  introv x
  skip
  rw [← e.apply_symm_apply x]
  apply RingHom.is_integral_map
#align ring_hom.is_integral_respects_iso RingHom.is_integral_respects_iso

theorem is_integral_stable_under_base_change :
    StableUnderBaseChange fun R S _ _ f => f.is_integral :=
  by
  refine' stable_under_base_change.mk _ is_integral_respects_iso _
  introv h x
  skip
  apply TensorProduct.induction_on x
  · apply is_integral_zero
  · intro x y
    exact IsIntegral.tmul x (h y)
  · intro x y hx hy
    exact is_integral_add _ hx hy
#align ring_hom.is_integral_stable_under_base_change RingHom.is_integral_stable_under_base_change

end RingHom

