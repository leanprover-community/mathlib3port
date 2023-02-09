/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou

! This file was ported from Lean 3 source module category_theory.localization.opposite
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.CategoryTheory.Localization.Predicate

/-!

# Localization of the opposite category

If a functor `L : C ⥤ D` is a localization functor for `W : morphism_property C`, it
is shown in this file that `L.op : Cᵒᵖ ⥤ Dᵒᵖ` is also a localization functor.

-/


noncomputable section

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory

variable {C D : Type _} [Category C] [Category D] {L : C ⥤ D} {W : MorphismProperty C}

namespace Localization

/-- If `L : C ⥤ D` satisfies the universal property of the localisation
for `W : morphism_property C`, then `L.op` also does. -/
def StrictUniversalPropertyFixedTarget.op {E : Type _} [Category E]
    (h : StrictUniversalPropertyFixedTarget L W Eᵒᵖ) :
    StrictUniversalPropertyFixedTarget L.op W.op E
    where
  inverts := h.inverts.op
  lift F hF := (h.lift F.rightOp hF.rightOp).leftOp
  fac F hF := by
    convert congr_arg Functor.leftOp (h.fac F.right_op hF.right_op)
    exact F.right_op_left_op_eq.symm
  uniq F₁ F₂ eq :=
    by
    suffices F₁.right_op = F₂.right_op by
      rw [← F₁.right_op_left_op_eq, ← F₂.right_op_left_op_eq, this]
    have eq' := congr_arg Functor.rightOp eq
    exact h.uniq _ _ eq'
#align category_theory.localization.strict_universal_property_fixed_target.op CategoryTheory.Localization.StrictUniversalPropertyFixedTarget.op

instance isLocalizationOp : W.q.op.IsLocalization W.op :=
  Functor.IsLocalization.mk' W.q.op W.op (strictUniversalPropertyFixedTargetQ W _).op
    (strictUniversalPropertyFixedTargetQ W _).op
#align category_theory.localization.is_localization_op CategoryTheory.Localization.isLocalizationOp

end Localization

namespace Functor

instance IsLocalization.op [h : L.IsLocalization W] : L.op.IsLocalization W.op :=
  IsLocalization.ofEquivalenceTarget W.q.op W.op L.op (Localization.equivalenceFromModel L W).op
    (NatIso.op (Localization.qCompEquivalenceFromModelFunctorIso L W).symm)
#align category_theory.functor.is_localization.op CategoryTheory.Functor.IsLocalization.op

end Functor

end CategoryTheory

