/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.normed_space.indicator_function
! leanprover-community/mathlib commit 17ef379e997badd73e5eabb4d38f11919ab3c4b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Basic
import Mathbin.Algebra.IndicatorFunction

/-!
# Indicator function and norm

This file contains a few simple lemmas about `set.indicator` and `norm`.

## Tags
indicator, norm
-/


variable {α E : Type _} [SeminormedAddCommGroup E] {s t : Set α} (f : α → E) (a : α)

open Set

/- warning: norm_indicator_eq_indicator_norm -> norm_indicator_eq_indicator_norm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), Eq.{1} Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)))))) s f a)) (Set.indicator.{u1, 0} α Real Real.hasZero s (fun (a : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a)) a)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), Eq.{1} Real (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)))))) s f a)) (Set.indicator.{u1, 0} α Real Real.instZeroReal s (fun (a : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (f a)) a)
Case conversion may be inaccurate. Consider using '#align norm_indicator_eq_indicator_norm norm_indicator_eq_indicator_normₓ'. -/
theorem norm_indicator_eq_indicator_norm : ‖indicator s f a‖ = indicator s (fun a => ‖f a‖) a :=
  flip congr_fun a (indicator_comp_of_zero norm_zero).symm
#align norm_indicator_eq_indicator_norm norm_indicator_eq_indicator_norm

/- warning: nnnorm_indicator_eq_indicator_nnnorm -> nnnorm_indicator_eq_indicator_nnnorm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), Eq.{1} NNReal (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (Set.indicator.{u1, u2} α E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)))))) s f a)) (Set.indicator.{u1, 0} α NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) s (fun (a : α) => NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f a)) a)
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), Eq.{1} NNReal (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (Set.indicator.{u1, u2} α E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)))))) s f a)) (Set.indicator.{u1, 0} α NNReal instNNRealZero s (fun (a : α) => NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)) (f a)) a)
Case conversion may be inaccurate. Consider using '#align nnnorm_indicator_eq_indicator_nnnorm nnnorm_indicator_eq_indicator_nnnormₓ'. -/
theorem nnnorm_indicator_eq_indicator_nnnorm :
    ‖indicator s f a‖₊ = indicator s (fun a => ‖f a‖₊) a :=
  flip congr_fun a (indicator_comp_of_zero nnnorm_zero).symm
#align nnnorm_indicator_eq_indicator_nnnorm nnnorm_indicator_eq_indicator_nnnorm

/- warning: norm_indicator_le_of_subset -> norm_indicator_le_of_subset is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} {t : Set.{u1} α}, (HasSubset.Subset.{u1} (Set.{u1} α) (Set.hasSubset.{u1} α) s t) -> (forall (f : α -> E) (a : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)))))) s f a)) (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)))))) t f a)))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {s : Set.{u2} α} {t : Set.{u2} α}, (HasSubset.Subset.{u2} (Set.{u2} α) (Set.instHasSubsetSet.{u2} α) s t) -> (forall (f : α -> E) (a : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (Set.indicator.{u2, u1} α E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) s f a)) (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (Set.indicator.{u2, u1} α E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (SeminormedAddCommGroup.toAddCommGroup.{u1} E _inst_1)))))) t f a)))
Case conversion may be inaccurate. Consider using '#align norm_indicator_le_of_subset norm_indicator_le_of_subsetₓ'. -/
theorem norm_indicator_le_of_subset (h : s ⊆ t) (f : α → E) (a : α) :
    ‖indicator s f a‖ ≤ ‖indicator t f a‖ :=
  by
  simp only [norm_indicator_eq_indicator_norm]
  exact indicator_le_indicator_of_subset ‹_› (fun _ => norm_nonneg _) _
#align norm_indicator_le_of_subset norm_indicator_le_of_subset

/- warning: indicator_norm_le_norm_self -> indicator_norm_le_norm_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), LE.le.{0} Real Real.hasLe (Set.indicator.{u1, 0} α Real Real.hasZero s (fun (a : α) => Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a)) a) (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a))
but is expected to have type
  forall {α : Type.{u2}} {E : Type.{u1}} [_inst_1 : SeminormedAddCommGroup.{u1} E] {s : Set.{u2} α} (f : α -> E) (a : α), LE.le.{0} Real Real.instLEReal (Set.indicator.{u2, 0} α Real Real.instZeroReal s (fun (a : α) => Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f a)) a) (Norm.norm.{u1} E (SeminormedAddCommGroup.toNorm.{u1} E _inst_1) (f a))
Case conversion may be inaccurate. Consider using '#align indicator_norm_le_norm_self indicator_norm_le_norm_selfₓ'. -/
theorem indicator_norm_le_norm_self : indicator s (fun a => ‖f a‖) a ≤ ‖f a‖ :=
  indicator_le_self' (fun _ _ => norm_nonneg _) a
#align indicator_norm_le_norm_self indicator_norm_le_norm_self

/- warning: norm_indicator_le_norm_self -> norm_indicator_le_norm_self is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), LE.le.{0} Real Real.hasLe (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (SeminormedAddGroup.toAddGroup.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E _inst_1)))))) s f a)) (Norm.norm.{u2} E (SeminormedAddCommGroup.toHasNorm.{u2} E _inst_1) (f a))
but is expected to have type
  forall {α : Type.{u1}} {E : Type.{u2}} [_inst_1 : SeminormedAddCommGroup.{u2} E] {s : Set.{u1} α} (f : α -> E) (a : α), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (Set.indicator.{u1, u2} α E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E _inst_1)))))) s f a)) (Norm.norm.{u2} E (SeminormedAddCommGroup.toNorm.{u2} E _inst_1) (f a))
Case conversion may be inaccurate. Consider using '#align norm_indicator_le_norm_self norm_indicator_le_norm_selfₓ'. -/
theorem norm_indicator_le_norm_self : ‖indicator s f a‖ ≤ ‖f a‖ :=
  by
  rw [norm_indicator_eq_indicator_norm]
  apply indicator_norm_le_norm_self
#align norm_indicator_le_norm_self norm_indicator_le_norm_self

