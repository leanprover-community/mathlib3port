/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Localization.Predicate

#align_import category_theory.localization.opposite from "leanprover-community/mathlib"@"31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0"

/-!

# Localization of the opposite category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

If a functor `L : C ⥤ D` is a localization functor for `W : morphism_property C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

#print CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.op /-
/-- If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : morphism_property C`, then `L.op` also does. -/
def StrictUniversalPropertyFixedTarget.op {E : Type _} [Category E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E
    where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert congr_arg functor.left_op (h.fac F.right_op hF.right_op)
    exact F.right_op_left_op_eq.symm
  uniq F₁ F₂ eq :=
    by
    suffices F₁.right_op = F₂.right_op by
      rw [← F₁.right_op_left_op_eq, ← F₂.right_op_left_op_eq, this]
    have eq' := congr_arg functor.right_op Eq
    exact h.uniq _ _ eq'
#align category_theory.localization.strict_universal_property_fixed_target.op CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.op
-/

#print CategoryTheory.Localization.isLocalization_op /-
instance isLocalization_op : W.Q.op.IsLocalizationₓ W.op :=
  Functor.IsLocalization.mk' W.Q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op
#align category_theory.localization.is_localization_op CategoryTheory.Localization.isLocalization_op
-/

end Localization

namespace Functor

#print CategoryTheory.Functor.IsLocalization.op /-
instance IsLocalization.op [h : L.IsLocalizationₓ W] : L.op.IsLocalizationₓ W.op :=
  IsLocalization.of_equivalence_target W.Q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)
#align category_theory.functor.is_localization.op CategoryTheory.Functor.IsLocalization.op
-/

end Functor

end CategoryTheory

