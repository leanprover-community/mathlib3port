/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathbin.RingTheory.LocalProperties

/-!

# The meta properties of finite ring homomorphisms.

-/


namespace RingHom

open TensorProduct

open TensorProduct Algebra.TensorProduct

theorem finiteStableUnderComposition : StableUnderComposition @Finite := by
  introv R hf hg
  exact hg.comp hf
#align ring_hom.finite_stable_under_composition RingHom.finiteStableUnderComposition

theorem finiteRespectsIso : RespectsIso @Finite := by
  apply finite_stable_under_composition.respects_iso
  intros
  exact Finite.of_surjective _ e.to_equiv.surjective
#align ring_hom.finite_respects_iso RingHom.finiteRespectsIso

theorem finiteStableUnderBaseChange : StableUnderBaseChange @Finite := by
  classical introv R h
    replace h : Module.Finite R T := by
      convert h
      ext
      rw [Algebra.smul_def]
      rfl
    · change Module.Finite _ _
      convert this
      ext
      rw [Algebra.smul_def]
      rfl
      
#align ring_hom.finite_stable_under_base_change RingHom.finiteStableUnderBaseChange

end RingHom

