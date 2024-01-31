/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import RingTheory.RingHomProperties

#align_import ring_theory.ring_hom.finite from "leanprover-community/mathlib"@"8af7091a43227e179939ba132e54e54e9f3b089a"

/-!

# The meta properties of finite ring homomorphisms.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/


namespace RingHom

open scoped TensorProduct

open TensorProduct Algebra.TensorProduct

#print RingHom.finite_stableUnderComposition /-
theorem finite_stableUnderComposition : StableUnderComposition @Finite := by introv R hf hg;
  exact hg.comp hf
#align ring_hom.finite_stable_under_composition RingHom.finite_stableUnderComposition
-/

#print RingHom.finite_respectsIso /-
theorem finite_respectsIso : RespectsIso @Finite :=
  by
  apply finite_stable_under_composition.respects_iso
  intros
  exact Finite.of_surjective _ e.to_equiv.surjective
#align ring_hom.finite_respects_iso RingHom.finite_respectsIso
-/

#print RingHom.finite_stableUnderBaseChange /-
theorem finite_stableUnderBaseChange : StableUnderBaseChange @Finite :=
  by
  refine' stable_under_base_change.mk _ finite_respects_iso _
  classical
#align ring_hom.finite_stable_under_base_change RingHom.finite_stableUnderBaseChange
-/

end RingHom

