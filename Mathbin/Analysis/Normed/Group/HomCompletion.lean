/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module analysis.normed.group.hom_completion
! leanprover-community/mathlib commit 69c6a5a12d8a2b159f20933e60115a4f2de62b58
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Given two (semi) normed groups `G` and `H` and a normed group hom `f : normed_add_group_hom G H`,
we build and study a normed group hom
`f.completion  : normed_add_group_hom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `normed_add_group_hom.completion`: see the discussion above.
* `normed_add_comm_group.to_compl : normed_add_group_hom G (completion G)`: the canonical map from
  `G` to its completion, as a normed group hom
* `normed_add_group_hom.completion_to_compl`: the above diagram indeed commutes.
* `normed_add_group_hom.norm_completion`: `‖f.completion‖ = ‖f‖`
* `normed_add_group_hom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of
  the kernel of `f`.
* `normed_add_group_hom.ker_completion`: the kernel of `f.completion` is the closure of the image of
  the kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `normed_add_group_hom.extension` : if `H` is complete, the extension of
  `f : normed_add_group_hom G H` to a `normed_add_group_hom (completion G) H`.
-/


noncomputable section

open Set NormedAddGroupHom UniformSpace

section Completion

variable {G : Type _} [SeminormedAddCommGroup G]

variable {H : Type _} [SeminormedAddCommGroup H]

variable {K : Type _} [SeminormedAddCommGroup K]

/- warning: normed_add_group_hom.completion -> NormedAddGroupHom.completion is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H], (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) -> (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H], (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) -> (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} H _inst_2)))
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion NormedAddGroupHom.completionₓ'. -/
/-- The normed group hom induced between completions. -/
def NormedAddGroupHom.completion (f : NormedAddGroupHom G H) :
    NormedAddGroupHom (Completion G) (Completion H) :=
  { f.toAddMonoidHom.Completion f.Continuous with
    bound' := by
      use ‖f‖
      intro y
      apply completion.induction_on y
      ·
        exact
          isClosed_le
            (continuous_norm.comp <| f.to_add_monoid_hom.continuous_completion f.continuous)
            (continuous_const.mul continuous_norm)
      · intro x
        change ‖f.to_add_monoid_hom.completion _ ↑x‖ ≤ ‖f‖ * ‖↑x‖
        rw [f.to_add_monoid_hom.completion_coe f.continuous]
        simp only [completion.norm_coe]
        exact f.le_op_norm x }
#align normed_add_group_hom.completion NormedAddGroupHom.completion

/- warning: normed_add_group_hom.completion_def -> NormedAddGroupHom.completion_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_def NormedAddGroupHom.completion_defₓ'. -/
theorem NormedAddGroupHom.completion_def (f : NormedAddGroupHom G H) (x : Completion G) :
    f.Completion x = Completion.map f x :=
  rfl
#align normed_add_group_hom.completion_def NormedAddGroupHom.completion_def

/- warning: normed_add_group_hom.completion_coe_to_fun -> NormedAddGroupHom.completion_coe_to_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_coe_to_fun NormedAddGroupHom.completion_coe_to_funₓ'. -/
@[simp]
theorem NormedAddGroupHom.completion_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.Completion : Completion G → Completion H) = Completion.map f := by ext x;
  exact NormedAddGroupHom.completion_def f x
#align normed_add_group_hom.completion_coe_to_fun NormedAddGroupHom.completion_coe_to_fun

/- warning: normed_add_group_hom.completion_coe -> NormedAddGroupHom.completion_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_coe NormedAddGroupHom.completion_coeₓ'. -/
@[simp]
theorem NormedAddGroupHom.completion_coe (f : NormedAddGroupHom G H) (g : G) :
    f.Completion g = f g :=
  Completion.map_coe f.UniformContinuous _
#align normed_add_group_hom.completion_coe NormedAddGroupHom.completion_coe

/- warning: normed_add_group_hom_completion_hom -> normedAddGroupHomCompletionHom is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom_completion_hom normedAddGroupHomCompletionHomₓ'. -/
/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedAddGroupHomCompletionHom :
    NormedAddGroupHom G H →+ NormedAddGroupHom (Completion G) (Completion H)
    where
  toFun := NormedAddGroupHom.completion
  map_zero' := by
    apply to_add_monoid_hom_injective
    exact AddMonoidHom.completion_zero
  map_add' f g := by
    apply to_add_monoid_hom_injective
    exact f.to_add_monoid_hom.completion_add g.to_add_monoid_hom f.continuous g.continuous
#align normed_add_group_hom_completion_hom normedAddGroupHomCompletionHom

/- warning: normed_add_group_hom.completion_id -> NormedAddGroupHom.completion_id is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], Eq.{succ u1} (NormedAddGroupHom.{u1, u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))) (NormedAddGroupHom.completion.{u1, u1} G _inst_1 G _inst_1 (NormedAddGroupHom.id.{u1} G _inst_1)) (NormedAddGroupHom.id.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], Eq.{succ u1} (NormedAddGroupHom.{u1, u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))) (NormedAddGroupHom.completion.{u1, u1} G _inst_1 G _inst_1 (NormedAddGroupHom.id.{u1} G _inst_1)) (NormedAddGroupHom.id.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1)))
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_id NormedAddGroupHom.completion_idₓ'. -/
@[simp]
theorem NormedAddGroupHom.completion_id :
    (NormedAddGroupHom.id G).Completion = NormedAddGroupHom.id (Completion G) :=
  by
  ext x
  rw [NormedAddGroupHom.completion_def, NormedAddGroupHom.coe_id, completion.map_id]
  rfl
#align normed_add_group_hom.completion_id NormedAddGroupHom.completion_id

/- warning: normed_add_group_hom.completion_comp -> NormedAddGroupHom.completion_comp is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] {K : Type.{u3}} [_inst_3 : SeminormedAddCommGroup.{u3} K] (f : NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) (g : NormedAddGroupHom.{u2, u3} H K _inst_2 _inst_3), Eq.{max (succ u1) (succ u3)} (NormedAddGroupHom.{u1, u3} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u3} K (PseudoMetricSpace.toUniformSpace.{u3} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} K _inst_3))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} (UniformSpace.Completion.{u3} K (PseudoMetricSpace.toUniformSpace.{u3} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} K _inst_3))) (UniformSpace.Completion.normedAddCommGroup.{u3} K _inst_3))) (NormedAddGroupHom.comp.{u1, u2, u3} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.{u3} K (PseudoMetricSpace.toUniformSpace.{u3} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} K _inst_3))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} (UniformSpace.Completion.{u3} K (PseudoMetricSpace.toUniformSpace.{u3} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} K _inst_3))) (UniformSpace.Completion.normedAddCommGroup.{u3} K _inst_3)) (NormedAddGroupHom.completion.{u2, u3} H _inst_2 K _inst_3 g) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 f)) (NormedAddGroupHom.completion.{u1, u3} G _inst_1 K _inst_3 (NormedAddGroupHom.comp.{u1, u2, u3} G H K _inst_1 _inst_2 _inst_3 g f))
but is expected to have type
  forall {G : Type.{u3}} [_inst_1 : SeminormedAddCommGroup.{u3} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] {K : Type.{u1}} [_inst_3 : SeminormedAddCommGroup.{u1} K] (f : NormedAddGroupHom.{u3, u2} G H _inst_1 _inst_2) (g : NormedAddGroupHom.{u2, u1} H K _inst_2 _inst_3), Eq.{max (succ u3) (succ u1)} (NormedAddGroupHom.{u3, u1} (UniformSpace.Completion.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G _inst_1))) (UniformSpace.Completion.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} K _inst_3))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} (UniformSpace.Completion.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u3} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} K _inst_3))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} K _inst_3))) (NormedAddGroupHom.comp.{u3, u2, u1} (UniformSpace.Completion.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} K _inst_3))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u3} (UniformSpace.Completion.{u3} G (PseudoMetricSpace.toUniformSpace.{u3} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u3} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u3} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} H _inst_2)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} K (PseudoMetricSpace.toUniformSpace.{u1} K (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} K _inst_3))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} K _inst_3)) (NormedAddGroupHom.completion.{u2, u1} H _inst_2 K _inst_3 g) (NormedAddGroupHom.completion.{u3, u2} G _inst_1 H _inst_2 f)) (NormedAddGroupHom.completion.{u3, u1} G _inst_1 K _inst_3 (NormedAddGroupHom.comp.{u3, u2, u1} G H K _inst_1 _inst_2 _inst_3 g f))
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_comp NormedAddGroupHom.completion_compₓ'. -/
theorem NormedAddGroupHom.completion_comp (f : NormedAddGroupHom G H) (g : NormedAddGroupHom H K) :
    g.Completion.comp f.Completion = (g.comp f).Completion :=
  by
  ext x
  rw [NormedAddGroupHom.coe_comp, NormedAddGroupHom.completion_def,
    NormedAddGroupHom.completion_coe_to_fun, NormedAddGroupHom.completion_coe_to_fun,
    completion.map_comp (NormedAddGroupHom.uniformContinuous _)
      (NormedAddGroupHom.uniformContinuous _)]
  rfl
#align normed_add_group_hom.completion_comp NormedAddGroupHom.completion_comp

/- warning: normed_add_group_hom.completion_neg -> NormedAddGroupHom.completion_neg is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] (f : NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 (Neg.neg.{max u1 u2} (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) (NormedAddGroupHom.hasNeg.{u1, u2} G H _inst_1 _inst_2) f)) (Neg.neg.{max u1 u2} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.hasNeg.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 f))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} G] {H : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} H] (f : NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.completion.{u2, u1} G _inst_1 H _inst_2 (Neg.neg.{max u2 u1} (NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2) (NormedAddGroupHom.neg.{u2, u1} G H _inst_1 _inst_2) f)) (Neg.neg.{max u2 u1} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.neg.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.completion.{u2, u1} G _inst_1 H _inst_2 f))
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_neg NormedAddGroupHom.completion_negₓ'. -/
theorem NormedAddGroupHom.completion_neg (f : NormedAddGroupHom G H) :
    (-f).Completion = -f.Completion :=
  map_neg (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f
#align normed_add_group_hom.completion_neg NormedAddGroupHom.completion_neg

/- warning: normed_add_group_hom.completion_add -> NormedAddGroupHom.completion_add is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_add NormedAddGroupHom.completion_addₓ'. -/
theorem NormedAddGroupHom.completion_add (f g : NormedAddGroupHom G H) :
    (f + g).Completion = f.Completion + g.Completion :=
  normedAddGroupHomCompletionHom.map_add f g
#align normed_add_group_hom.completion_add NormedAddGroupHom.completion_add

/- warning: normed_add_group_hom.completion_sub -> NormedAddGroupHom.completion_sub is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_sub NormedAddGroupHom.completion_subₓ'. -/
theorem NormedAddGroupHom.completion_sub (f g : NormedAddGroupHom G H) :
    (f - g).Completion = f.Completion - g.Completion :=
  map_sub (normedAddGroupHomCompletionHom : NormedAddGroupHom G H →+ _) f g
#align normed_add_group_hom.completion_sub NormedAddGroupHom.completion_sub

/- warning: normed_add_group_hom.zero_completion -> NormedAddGroupHom.zero_completion is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H], Eq.{max (succ u1) (succ u2)} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 (OfNat.ofNat.{max u1 u2} (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) 0 (OfNat.mk.{max u1 u2} (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) 0 (Zero.zero.{max u1 u2} (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) (NormedAddGroupHom.hasZero.{u1, u2} G H _inst_1 _inst_2))))) (OfNat.ofNat.{max u1 u2} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) 0 (OfNat.mk.{max u1 u2} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) 0 (Zero.zero.{max u1 u2} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.hasZero.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))))))
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} G] {H : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} H], Eq.{max (succ u2) (succ u1)} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.completion.{u2, u1} G _inst_1 H _inst_2 (OfNat.ofNat.{max u2 u1} (NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2) 0 (Zero.toOfNat0.{max u2 u1} (NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2) (NormedAddGroupHom.zero.{u2, u1} G H _inst_1 _inst_2)))) (OfNat.ofNat.{max u2 u1} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) 0 (Zero.toOfNat0.{max u2 u1} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.zero.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2)))))
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.zero_completion NormedAddGroupHom.zero_completionₓ'. -/
@[simp]
theorem NormedAddGroupHom.zero_completion : (0 : NormedAddGroupHom G H).Completion = 0 :=
  normedAddGroupHomCompletionHom.map_zero
#align normed_add_group_hom.zero_completion NormedAddGroupHom.zero_completion

/- warning: normed_add_comm_group.to_compl -> NormedAddCommGroup.toCompl is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.to_compl NormedAddCommGroup.toComplₓ'. -/
/-- The map from a normed group to its completion, as a normed group hom. -/
def NormedAddCommGroup.toCompl : NormedAddGroupHom G (Completion G)
    where
  toFun := coe
  map_add' := Completion.toCompl.map_add
  bound' := ⟨1, by simp [le_refl]⟩
#align normed_add_comm_group.to_compl NormedAddCommGroup.toCompl

open NormedAddCommGroup

#print NormedAddCommGroup.norm_toCompl /-
theorem NormedAddCommGroup.norm_toCompl (x : G) : ‖toCompl x‖ = ‖x‖ :=
  Completion.norm_coe x
#align normed_add_comm_group.norm_to_compl NormedAddCommGroup.norm_toCompl
-/

/- warning: normed_add_comm_group.dense_range_to_compl -> NormedAddCommGroup.denseRange_toCompl is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], DenseRange.{u1, u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (PseudoMetricSpace.toUniformSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))))) G (coeFn.{succ u1, succ u1} (NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))) (fun (_x : NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))) => G -> (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1)))) (NormedAddGroupHom.hasCoeToFun.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1))) (NormedAddCommGroup.toCompl.{u1} G _inst_1))
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G], DenseRange.{u1, u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.toTopologicalSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (PseudoMetricSpace.toUniformSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))))) G (FunLike.coe.{succ u1, succ u1, succ u1} (NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))) G (fun (_x : G) => UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddHomClass.toFunLike.{u1, u1, u1} (NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))) G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddZeroClass.toAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (SeminormedAddGroup.toAddGroup.{u1} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} G _inst_1)))))) (AddZeroClass.toAdd.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddMonoid.toAddZeroClass.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SubNegMonoid.toAddMonoid.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddGroup.toSubNegMonoid.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddGroup.toAddGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1)))))))) (AddMonoidHomClass.toAddHomClass.{u1, u1, u1} (NormedAddGroupHom.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))) G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (SeminormedAddGroup.toAddGroup.{u1} G (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} G _inst_1))))) (AddMonoid.toAddZeroClass.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SubNegMonoid.toAddMonoid.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (AddGroup.toSubNegMonoid.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddGroup.toAddGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))))))) (NormedAddGroupHom.toAddMonoidHomClass.{u1, u1} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1))))) (NormedAddCommGroup.toCompl.{u1} G _inst_1))
Case conversion may be inaccurate. Consider using '#align normed_add_comm_group.dense_range_to_compl NormedAddCommGroup.denseRange_toComplₓ'. -/
theorem NormedAddCommGroup.denseRange_toCompl : DenseRange (toCompl : G → Completion G) :=
  Completion.denseInducing_coe.dense
#align normed_add_comm_group.dense_range_to_compl NormedAddCommGroup.denseRange_toCompl

/- warning: normed_add_group_hom.completion_to_compl -> NormedAddGroupHom.completion_toCompl is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] (f : NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2), Eq.{max (succ u1) (succ u2)} (NormedAddGroupHom.{u1, u2} G (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.comp.{u1, u1, u2} G (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2)) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 f) (NormedAddCommGroup.toCompl.{u1} G _inst_1)) (NormedAddGroupHom.comp.{u1, u2, u2} G H (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) _inst_1 _inst_2 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2)) (NormedAddCommGroup.toCompl.{u2} H _inst_2) f)
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} G] {H : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} H] (f : NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2), Eq.{max (succ u2) (succ u1)} (NormedAddGroupHom.{u2, u1} G (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.comp.{u2, u2, u1} G (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) _inst_1 (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2)) (NormedAddGroupHom.completion.{u2, u1} G _inst_1 H _inst_2 f) (NormedAddCommGroup.toCompl.{u2} G _inst_1)) (NormedAddGroupHom.comp.{u2, u1, u1} G H (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) _inst_1 _inst_2 (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2)) (NormedAddCommGroup.toCompl.{u1} H _inst_2) f)
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.completion_to_compl NormedAddGroupHom.completion_toComplₓ'. -/
@[simp]
theorem NormedAddGroupHom.completion_toCompl (f : NormedAddGroupHom G H) :
    f.Completion.comp toCompl = toCompl.comp f :=
  by
  ext x
  change f.completion x = _
  simpa
#align normed_add_group_hom.completion_to_compl NormedAddGroupHom.completion_toCompl

/- warning: normed_add_group_hom.norm_completion -> NormedAddGroupHom.norm_completion is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] (f : NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2), Eq.{1} Real (Norm.norm.{max u1 u2} (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.hasOpNorm.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))) (UniformSpace.Completion.normedAddCommGroup.{u2} H _inst_2))) (NormedAddGroupHom.completion.{u1, u2} G _inst_1 H _inst_2 f)) (Norm.norm.{max u1 u2} (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) (NormedAddGroupHom.hasOpNorm.{u1, u2} G H _inst_1 _inst_2) f)
but is expected to have type
  forall {G : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} G] {H : Type.{u1}} [_inst_2 : SeminormedAddCommGroup.{u1} H] (f : NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2), Eq.{1} Real (Norm.norm.{max u2 u1} (NormedAddGroupHom.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.hasOpNorm.{u2, u1} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} G (PseudoMetricSpace.toUniformSpace.{u2} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} G _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} H (PseudoMetricSpace.toUniformSpace.{u1} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} H _inst_2))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} H _inst_2))) (NormedAddGroupHom.completion.{u2, u1} G _inst_1 H _inst_2 f)) (Norm.norm.{max u2 u1} (NormedAddGroupHom.{u2, u1} G H _inst_1 _inst_2) (NormedAddGroupHom.hasOpNorm.{u2, u1} G H _inst_1 _inst_2) f)
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.norm_completion NormedAddGroupHom.norm_completionₓ'. -/
@[simp]
theorem NormedAddGroupHom.norm_completion (f : NormedAddGroupHom G H) : ‖f.Completion‖ = ‖f‖ :=
  by
  apply f.completion.op_norm_eq_of_bounds (norm_nonneg _)
  · intro x
    apply completion.induction_on x
    · apply isClosed_le
      continuity
    · intro g
      simp [f.le_op_norm g]
  · intro N N_nonneg hN
    apply f.op_norm_le_bound N_nonneg
    intro x
    simpa using hN x
#align normed_add_group_hom.norm_completion NormedAddGroupHom.norm_completion

/- warning: normed_add_group_hom.ker_le_ker_completion -> NormedAddGroupHom.ker_le_ker_completion is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.ker_le_ker_completion NormedAddGroupHom.ker_le_ker_completionₓ'. -/
theorem NormedAddGroupHom.ker_le_ker_completion (f : NormedAddGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.Completion.ker :=
  by
  intro a h
  replace h : ∃ y : f.ker, to_compl (y : G) = a; · simpa using h
  rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩
  rw [f.mem_ker] at g_in
  change f.completion (g : completion G) = 0
  simp [NormedAddGroupHom.mem_ker, f.completion_coe g, g_in, completion.coe_zero]
#align normed_add_group_hom.ker_le_ker_completion NormedAddGroupHom.ker_le_ker_completion

/- warning: normed_add_group_hom.ker_completion -> NormedAddGroupHom.ker_completion is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.ker_completion NormedAddGroupHom.ker_completionₓ'. -/
theorem NormedAddGroupHom.ker_completion {f : NormedAddGroupHom G H} {C : ℝ}
    (h : f.SurjectiveOnWith f.range C) :
    (f.Completion.ker : Set <| Completion G) = closure (toCompl.comp <| incl f.ker).range :=
  by
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  apply le_antisymm
  · intro hatg hatg_in
    rw [SeminormedAddCommGroup.mem_closure_iff]
    intro ε ε_pos
    have hCf : 0 ≤ C' * ‖f‖ := (zero_le_mul_left C'_pos).mpr (norm_nonneg f)
    have ineq : 0 < 1 + C' * ‖f‖ := by linarith
    set δ := ε / (1 + C' * ‖f‖)
    have δ_pos : δ > 0 := div_pos ε_pos ineq
    obtain ⟨_, ⟨g : G, rfl⟩, hg : ‖hatg - g‖ < δ⟩ :=
      seminormed_add_comm_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ
        δ_pos
    obtain ⟨g' : G, hgg' : f g' = f g, hfg : ‖g'‖ ≤ C' * ‖f g‖⟩ := hC' (f g) (mem_range_self g)
    have mem_ker : g - g' ∈ f.ker := by rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
    have : ‖f g‖ ≤ ‖f‖ * ‖hatg - g‖
    calc
      ‖f g‖ = ‖f.completion g‖ := by rw [f.completion_coe, completion.norm_coe]
      _ = ‖f.completion g - 0‖ := by rw [sub_zero _]
      _ = ‖f.completion g - f.completion hatg‖ := by rw [(f.completion.mem_ker _).mp hatg_in]
      _ = ‖f.completion (g - hatg)‖ := by rw [map_sub]
      _ ≤ ‖f.completion‖ * ‖(g : completion G) - hatg‖ := (f.completion.le_op_norm _)
      _ = ‖f‖ * ‖hatg - g‖ := by rw [norm_sub_rev, f.norm_completion]
      
    have : ‖(g' : completion G)‖ ≤ C' * ‖f‖ * ‖hatg - g‖
    calc
      ‖(g' : completion G)‖ = ‖g'‖ := completion.norm_coe _
      _ ≤ C' * ‖f g‖ := hfg
      _ ≤ C' * ‖f‖ * ‖hatg - g‖ := by
        rw [mul_assoc]
        exact (mul_le_mul_left C'_pos).mpr this
      
    refine' ⟨g - g', _, _⟩
    · norm_cast
      rw [NormedAddGroupHom.comp_range]
      apply AddSubgroup.mem_map_of_mem
      simp only [incl_range, mem_ker]
    ·
      calc
        ‖hatg - (g - g')‖ = ‖hatg - g + g'‖ := by abel
        _ ≤ ‖hatg - g‖ + ‖(g' : completion G)‖ := (norm_add_le _ _)
        _ < δ + C' * ‖f‖ * ‖hatg - g‖ := by linarith
        _ ≤ δ + C' * ‖f‖ * δ := (add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ)
        _ = (1 + C' * ‖f‖) * δ := by ring
        _ = ε := mul_div_cancel' _ ineq.ne.symm
        
  · rw [← f.completion.is_closed_ker.closure_eq]
    exact closure_mono f.ker_le_ker_completion
#align normed_add_group_hom.ker_completion NormedAddGroupHom.ker_completion

end Completion

section Extension

variable {G : Type _} [SeminormedAddCommGroup G]

variable {H : Type _} [SeminormedAddCommGroup H] [SeparatedSpace H] [CompleteSpace H]

/- warning: normed_add_group_hom.extension -> NormedAddGroupHom.extension is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] [_inst_3 : SeparatedSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))] [_inst_4 : CompleteSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))], (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) -> (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.normedAddCommGroup.{u1} G _inst_1)) _inst_2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} G] {H : Type.{u2}} [_inst_2 : SeminormedAddCommGroup.{u2} H] [_inst_3 : SeparatedSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))] [_inst_4 : CompleteSpace.{u2} H (PseudoMetricSpace.toUniformSpace.{u2} H (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} H _inst_2))], (NormedAddGroupHom.{u1, u2} G H _inst_1 _inst_2) -> (NormedAddGroupHom.{u1, u2} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) H (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (UniformSpace.Completion.{u1} G (PseudoMetricSpace.toUniformSpace.{u1} G (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} G _inst_1))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u1} G _inst_1)) _inst_2)
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.extension NormedAddGroupHom.extensionₓ'. -/
/-- If `H` is complete, the extension of `f : normed_add_group_hom G H` to a
`normed_add_group_hom (completion G) H`. -/
def NormedAddGroupHom.extension (f : NormedAddGroupHom G H) : NormedAddGroupHom (Completion G) H :=
  { f.toAddMonoidHom.extension f.Continuous with
    bound' :=
      by
      refine' ⟨‖f‖, fun v => completion.induction_on v (isClosed_le _ _) fun a => _⟩
      · exact Continuous.comp continuous_norm completion.continuous_extension
      · exact Continuous.mul continuous_const continuous_norm
      · rw [completion.norm_coe, AddMonoidHom.toFun_eq_coe, AddMonoidHom.extension_coe]
        exact le_op_norm f a }
#align normed_add_group_hom.extension NormedAddGroupHom.extension

/- warning: normed_add_group_hom.extension_def -> NormedAddGroupHom.extension_def is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.extension_def NormedAddGroupHom.extension_defₓ'. -/
theorem NormedAddGroupHom.extension_def (f : NormedAddGroupHom G H) (v : G) :
    f.extension v = Completion.extension f v :=
  rfl
#align normed_add_group_hom.extension_def NormedAddGroupHom.extension_def

/- warning: normed_add_group_hom.extension_coe -> NormedAddGroupHom.extension_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.extension_coe NormedAddGroupHom.extension_coeₓ'. -/
@[simp]
theorem NormedAddGroupHom.extension_coe (f : NormedAddGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.Continuous _
#align normed_add_group_hom.extension_coe NormedAddGroupHom.extension_coe

/- warning: normed_add_group_hom.extension_coe_to_fun -> NormedAddGroupHom.extension_coe_to_fun is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.extension_coe_to_fun NormedAddGroupHom.extension_coe_to_funₓ'. -/
theorem NormedAddGroupHom.extension_coe_to_fun (f : NormedAddGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl
#align normed_add_group_hom.extension_coe_to_fun NormedAddGroupHom.extension_coe_to_fun

/- warning: normed_add_group_hom.extension_unique -> NormedAddGroupHom.extension_unique is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align normed_add_group_hom.extension_unique NormedAddGroupHom.extension_uniqueₓ'. -/
theorem NormedAddGroupHom.extension_unique (f : NormedAddGroupHom G H)
    {g : NormedAddGroupHom (Completion G) H} (hg : ∀ v, f v = g v) : f.extension = g :=
  by
  ext v
  rw [NormedAddGroupHom.extension_coe_to_fun,
    completion.extension_unique f.uniform_continuous g.uniform_continuous fun a => hg a]
#align normed_add_group_hom.extension_unique NormedAddGroupHom.extension_unique

end Extension

