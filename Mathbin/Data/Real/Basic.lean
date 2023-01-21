/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn

! This file was ported from Lean 3 source module data.real.basic
! leanprover-community/mathlib commit 2445c98ae4b87eabebdde552593519b9b6dc350c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Bounds
import Mathbin.Algebra.Order.Archimedean
import Mathbin.Algebra.Star.Basic
import Mathbin.Data.Real.CauSeqCompletion

/-!
# Real numbers from Cauchy sequences

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines `ℝ` as the type of equivalence classes of Cauchy sequences of rational numbers.
This choice is motivated by how easy it is to prove that `ℝ` is a commutative ring, by simply
lifting everything to `ℚ`.
-/


assert_not_exists Finset

assert_not_exists Module

assert_not_exists Submonoid

open Pointwise

#print Real /-
/-- The type `ℝ` of real numbers constructed as equivalence classes of Cauchy sequences of rational
numbers. -/
structure Real where ofCauchy ::
  cauchy : CauSeq.Completion.Cauchy (abs : ℚ → ℚ)
#align real Real
-/

-- mathport name: exprℝ
notation "ℝ" => Real

attribute [pp_using_anonymous_constructor] Real

namespace CauSeq.Completion

/- warning: cau_seq.completion.of_rat_rat -> CauSeq.Completion.ofRat_rat is a dubious translation:
lean 3 declaration is
  forall {abv : Rat -> Rat} [_inst_1 : IsAbsoluteValue.{0, 0} Rat Rat.orderedSemiring Rat Rat.semiring abv] (q : Rat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (CauSeq.Completion.ofRat.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1 q) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (HasLiftT.mk.{1, 1} Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (CoeTCₓ.coe.{1, 1} Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (Rat.castCoe.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (CauSeq.Completion.Cauchy.hasRatCast.{0, 0} Rat Rat.linearOrderedField Rat Rat.divisionRing abv _inst_1)))) q)
but is expected to have type
  forall {abv : Rat -> Rat} [_inst_1 : IsAbsoluteValue.{0, 0} Rat Rat.instOrderedSemiringRat Rat Rat.semiring abv] (q : Rat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (CauSeq.Completion.ofRat.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1 q) (RatCast.ratCast.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) abv _inst_1) (CauSeq.Completion.instRatCastCauchyToRing.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat Rat.divisionRing abv _inst_1) q)
Case conversion may be inaccurate. Consider using '#align cau_seq.completion.of_rat_rat CauSeq.Completion.ofRat_ratₓ'. -/
-- this can't go in `data.real.cau_seq_completion` as the structure on `rat` isn't available
@[simp]
theorem ofRat_rat {abv : ℚ → ℚ} [IsAbsoluteValue abv] (q : ℚ) :
    ofRat (q : ℚ) = (q : @Cauchy _ _ _ _ abv _) :=
  rfl
#align cau_seq.completion.of_rat_rat CauSeq.Completion.ofRat_rat

end CauSeq.Completion

namespace Real

open CauSeq CauSeq.Completion

variable {x y : ℝ}

/- warning: real.ext_cauchy_iff -> Real.ext_cauchy_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, Iff (Eq.{1} Real x y) (Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy x) (Real.cauchy y))
but is expected to have type
  forall {x : Real} {y : Real}, Iff (Eq.{1} Real x y) (Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy x) (Real.cauchy y))
Case conversion may be inaccurate. Consider using '#align real.ext_cauchy_iff Real.ext_cauchy_iffₓ'. -/
theorem ext_cauchy_iff : ∀ {x y : Real}, x = y ↔ x.cauchy = y.cauchy
  | ⟨a⟩, ⟨b⟩ => by constructor <;> cc
#align real.ext_cauchy_iff Real.ext_cauchy_iff

/- warning: real.ext_cauchy -> Real.ext_cauchy is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy x) (Real.cauchy y)) -> (Eq.{1} Real x y)
but is expected to have type
  forall {x : Real} {y : Real}, (Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy x) (Real.cauchy y)) -> (Eq.{1} Real x y)
Case conversion may be inaccurate. Consider using '#align real.ext_cauchy Real.ext_cauchyₓ'. -/
theorem ext_cauchy {x y : Real} : x.cauchy = y.cauchy → x = y :=
  ext_cauchy_iff.2
#align real.ext_cauchy Real.ext_cauchy

/- warning: real.equiv_Cauchy -> Real.equivCauchy is a dubious translation:
lean 3 declaration is
  Equiv.{1, 1} Real (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))
but is expected to have type
  Equiv.{1, 1} Real (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))
Case conversion may be inaccurate. Consider using '#align real.equiv_Cauchy Real.equivCauchyₓ'. -/
/-- The real numbers are isomorphic to the quotient of Cauchy sequences on the rationals. -/
def equivCauchy : ℝ ≃ CauSeq.Completion.Cauchy abs :=
  ⟨Real.cauchy, Real.ofCauchy, fun ⟨_⟩ => rfl, fun _ => rfl⟩
#align real.equiv_Cauchy Real.equivCauchy

-- irreducible doesn't work for instances: https://github.com/leanprover-community/lean/issues/511
private irreducible_def zero : ℝ :=
  ⟨0⟩
#align real.zero real.zero

private irreducible_def one : ℝ :=
  ⟨1⟩
#align real.one real.one

private irreducible_def add : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a + b⟩
#align real.add real.add

private irreducible_def neg : ℝ → ℝ
  | ⟨a⟩ => ⟨-a⟩
#align real.neg real.neg

private irreducible_def mul : ℝ → ℝ → ℝ
  | ⟨a⟩, ⟨b⟩ => ⟨a * b⟩
#align real.mul real.mul

private noncomputable irreducible_def inv' : ℝ → ℝ
  | ⟨a⟩ => ⟨a⁻¹⟩
#align real.inv' real.inv'

instance : Zero ℝ :=
  ⟨zero⟩

instance : One ℝ :=
  ⟨one⟩

instance : Add ℝ :=
  ⟨add⟩

instance : Neg ℝ :=
  ⟨neg⟩

instance : Mul ℝ :=
  ⟨mul⟩

instance : Sub ℝ :=
  ⟨fun a b => a + -b⟩

noncomputable instance : Inv ℝ :=
  ⟨inv'⟩

/- warning: real.of_cauchy_zero clashes with real.ofCauchy_zero -> Real.ofCauchy_zero
warning: real.of_cauchy_zero -> Real.ofCauchy_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.ofCauchy (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 0 (OfNat.mk.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 0 (Zero.zero.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasZero.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.ofCauchy (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) 0 (Zero.toOfNat0.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instZeroCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_zero Real.ofCauchy_zeroₓ'. -/
theorem ofCauchy_zero : (⟨0⟩ : ℝ) = 0 :=
  show _ = zero by rw [zero]
#align real.of_cauchy_zero Real.ofCauchy_zero

/- warning: real.of_cauchy_one clashes with real.ofCauchy_one -> Real.ofCauchy_one
warning: real.of_cauchy_one -> Real.ofCauchy_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.ofCauchy (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 1 (OfNat.mk.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 1 (One.one.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasOne.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Real.ofCauchy (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) 1 (One.toOfNat1.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instOneCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_one Real.ofCauchy_oneₓ'. -/
theorem ofCauchy_one : (⟨1⟩ : ℝ) = 1 :=
  show _ = one by rw [one]
#align real.of_cauchy_one Real.ofCauchy_one

/- warning: real.of_cauchy_add clashes with real.ofCauchy_add -> Real.ofCauchy_add
warning: real.of_cauchy_add -> Real.ofCauchy_add is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)), Eq.{1} Real (Real.ofCauchy (HAdd.hAdd.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHAdd.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasAdd.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) a b)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.ofCauchy a) (Real.ofCauchy b))
but is expected to have type
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)), Eq.{1} Real (Real.ofCauchy (HAdd.hAdd.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHAdd.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instAddCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) a b)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.ofCauchy a) (Real.ofCauchy b))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_add Real.ofCauchy_addₓ'. -/
theorem ofCauchy_add (a b) : (⟨a + b⟩ : ℝ) = ⟨a⟩ + ⟨b⟩ :=
  show _ = add _ _ by rw [add]
#align real.of_cauchy_add Real.ofCauchy_add

/- warning: real.of_cauchy_neg clashes with real.ofCauchy_neg -> Real.ofCauchy_neg
warning: real.of_cauchy_neg -> Real.ofCauchy_neg is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)), Eq.{1} Real (Real.ofCauchy (Neg.neg.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasNeg.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) a)) (Neg.neg.{0} Real Real.hasNeg (Real.ofCauchy a))
but is expected to have type
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)), Eq.{1} Real (Real.ofCauchy (Neg.neg.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instNegCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) a)) (Neg.neg.{0} Real Real.instNegReal (Real.ofCauchy a))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_neg Real.ofCauchy_negₓ'. -/
theorem ofCauchy_neg (a) : (⟨-a⟩ : ℝ) = -⟨a⟩ :=
  show _ = neg _ by rw [neg]
#align real.of_cauchy_neg Real.ofCauchy_neg

/- warning: real.of_cauchy_sub clashes with real.ofCauchy_sub -> Real.ofCauchy_sub
warning: real.of_cauchy_sub -> Real.ofCauchy_sub is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)), Eq.{1} Real (Real.ofCauchy (HSub.hSub.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHSub.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasSub.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.ofCauchy a) (Real.ofCauchy b))
but is expected to have type
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)), Eq.{1} Real (Real.ofCauchy (HSub.hSub.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHSub.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instSubCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) a b)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.ofCauchy a) (Real.ofCauchy b))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_sub Real.ofCauchy_subₓ'. -/
theorem ofCauchy_sub (a b) : (⟨a - b⟩ : ℝ) = ⟨a⟩ - ⟨b⟩ :=
  by
  rw [sub_eq_add_neg, of_cauchy_add, of_cauchy_neg]
  rfl
#align real.of_cauchy_sub Real.ofCauchy_sub

/- warning: real.of_cauchy_mul clashes with real.ofCauchy_mul -> Real.ofCauchy_mul
warning: real.of_cauchy_mul -> Real.ofCauchy_mul is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)), Eq.{1} Real (Real.ofCauchy (HMul.hMul.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHMul.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasMul.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.ofCauchy a) (Real.ofCauchy b))
but is expected to have type
  forall (a : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (b : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)), Eq.{1} Real (Real.ofCauchy (HMul.hMul.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHMul.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instMulCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) a b)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.ofCauchy a) (Real.ofCauchy b))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_mul Real.ofCauchy_mulₓ'. -/
theorem ofCauchy_mul (a b) : (⟨a * b⟩ : ℝ) = ⟨a⟩ * ⟨b⟩ :=
  show _ = mul _ _ by rw [mul]
#align real.of_cauchy_mul Real.ofCauchy_mul

/- warning: real.of_cauchy_inv clashes with real.ofCauchy_inv -> Real.ofCauchy_inv
warning: real.of_cauchy_inv -> Real.ofCauchy_inv is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)}, Eq.{1} Real (Real.ofCauchy (Inv.inv.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasInv.{0, 0} Rat Rat.linearOrderedField Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) f)) (Inv.inv.{0} Real Real.hasInv (Real.ofCauchy f))
but is expected to have type
  forall {f : CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)}, Eq.{1} Real (Real.ofCauchy (Inv.inv.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instInvCauchyToRing.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) f)) (Inv.inv.{0} Real Real.instInvReal (Real.ofCauchy f))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_inv Real.ofCauchy_invₓ'. -/
theorem ofCauchy_inv {f} : (⟨f⁻¹⟩ : ℝ) = ⟨f⟩⁻¹ :=
  show _ = inv' _ by rw [inv']
#align real.of_cauchy_inv Real.ofCauchy_inv

/- warning: real.cauchy_zero -> Real.cauchy_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 0 (OfNat.mk.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 0 (Zero.zero.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasZero.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))
but is expected to have type
  Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) 0 (Zero.toOfNat0.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instZeroCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))
Case conversion may be inaccurate. Consider using '#align real.cauchy_zero Real.cauchy_zeroₓ'. -/
theorem cauchy_zero : (0 : ℝ).cauchy = 0 :=
  show zero.cauchy = 0 by rw [zero]
#align real.cauchy_zero Real.cauchy_zero

/- warning: real.cauchy_one -> Real.cauchy_one is a dubious translation:
lean 3 declaration is
  Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 1 (OfNat.mk.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) 1 (One.one.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasOne.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))
but is expected to have type
  Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) 1 (One.toOfNat1.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instOneCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))
Case conversion may be inaccurate. Consider using '#align real.cauchy_one Real.cauchy_oneₓ'. -/
theorem cauchy_one : (1 : ℝ).cauchy = 1 :=
  show one.cauchy = 1 by rw [one]
#align real.cauchy_one Real.cauchy_one

/- warning: real.cauchy_add -> Real.cauchy_add is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) a b)) (HAdd.hAdd.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHAdd.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasAdd.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) (Real.cauchy a) (Real.cauchy b))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) a b)) (HAdd.hAdd.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHAdd.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instAddCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) (Real.cauchy a) (Real.cauchy b))
Case conversion may be inaccurate. Consider using '#align real.cauchy_add Real.cauchy_addₓ'. -/
theorem cauchy_add : ∀ a b, (a + b : ℝ).cauchy = a.cauchy + b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (add _ _).cauchy = _ by rw [add]
#align real.cauchy_add Real.cauchy_add

/- warning: real.cauchy_neg -> Real.cauchy_neg is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (Neg.neg.{0} Real Real.hasNeg a)) (Neg.neg.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasNeg.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy a))
but is expected to have type
  forall (a : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (Neg.neg.{0} Real Real.instNegReal a)) (Neg.neg.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instNegCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy a))
Case conversion may be inaccurate. Consider using '#align real.cauchy_neg Real.cauchy_negₓ'. -/
theorem cauchy_neg : ∀ a, (-a : ℝ).cauchy = -a.cauchy
  | ⟨a⟩ => show (neg _).cauchy = _ by rw [neg]
#align real.cauchy_neg Real.cauchy_neg

/- warning: real.cauchy_mul -> Real.cauchy_mul is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) a b)) (HMul.hMul.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHMul.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasMul.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) (Real.cauchy a) (Real.cauchy b))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) a b)) (HMul.hMul.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHMul.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instMulCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) (Real.cauchy a) (Real.cauchy b))
Case conversion may be inaccurate. Consider using '#align real.cauchy_mul Real.cauchy_mulₓ'. -/
theorem cauchy_mul : ∀ a b, (a * b : ℝ).cauchy = a.cauchy * b.cauchy
  | ⟨a⟩, ⟨b⟩ => show (mul _ _).cauchy = _ by rw [mul]
#align real.cauchy_mul Real.cauchy_mul

/- warning: real.cauchy_sub -> Real.cauchy_sub is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) a b)) (HSub.hSub.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (instHSub.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasSub.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) (Real.cauchy a) (Real.cauchy b))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) a b)) (HSub.hSub.{0, 0, 0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (instHSub.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instSubCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) (Real.cauchy a) (Real.cauchy b))
Case conversion may be inaccurate. Consider using '#align real.cauchy_sub Real.cauchy_subₓ'. -/
theorem cauchy_sub : ∀ a b, (a - b : ℝ).cauchy = a.cauchy - b.cauchy
  | ⟨a⟩, ⟨b⟩ => by
    rw [sub_eq_add_neg, ← cauchy_neg, ← cauchy_add]
    rfl
#align real.cauchy_sub Real.cauchy_sub

/- warning: real.cauchy_inv -> Real.cauchy_inv is a dubious translation:
lean 3 declaration is
  forall (f : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy (Inv.inv.{0} Real Real.hasInv f)) (Inv.inv.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasInv.{0, 0} Rat Rat.linearOrderedField Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy f))
but is expected to have type
  forall (f : Real), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (Inv.inv.{0} Real Real.instInvReal f)) (Inv.inv.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instInvCauchyToRing.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy f))
Case conversion may be inaccurate. Consider using '#align real.cauchy_inv Real.cauchy_invₓ'. -/
theorem cauchy_inv : ∀ f, (f⁻¹ : ℝ).cauchy = f.cauchy⁻¹
  | ⟨f⟩ => show (inv' _).cauchy = _ by rw [inv']
#align real.cauchy_inv Real.cauchy_inv

instance : NatCast ℝ where natCast n := ⟨n⟩

instance : IntCast ℝ where intCast z := ⟨z⟩

instance : RatCast ℝ where ratCast q := ⟨q⟩

theorem ofCauchy_nat_cast (n : ℕ) : (⟨n⟩ : ℝ) = n :=
  rfl
#align real.of_cauchy_nat_cast Real.ofCauchy_nat_cast

theorem ofCauchy_int_cast (z : ℤ) : (⟨z⟩ : ℝ) = z :=
  rfl
#align real.of_cauchy_int_cast Real.ofCauchy_int_cast

theorem ofCauchy_rat_cast (q : ℚ) : (⟨q⟩ : ℝ) = q :=
  rfl
#align real.of_cauchy_rat_cast Real.ofCauchy_rat_cast

/- warning: real.cauchy_nat_cast -> Real.cauchy_natCast is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Real (HasLiftT.mk.{1, 1} Nat Real (CoeTCₓ.coe.{1, 1} Nat Real (Nat.castCoe.{0} Real Real.hasNatCast))) n)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (HasLiftT.mk.{1, 1} Nat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CoeTCₓ.coe.{1, 1} Nat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Nat.castCoe.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasNatCast.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))))) n)
but is expected to have type
  forall (n : Nat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (Nat.cast.{0} Real Real.natCast n)) (Nat.cast.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instNatCastCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) n)
Case conversion may be inaccurate. Consider using '#align real.cauchy_nat_cast Real.cauchy_natCastₓ'. -/
theorem cauchy_natCast (n : ℕ) : (n : ℝ).cauchy = n :=
  rfl
#align real.cauchy_nat_cast Real.cauchy_natCast

/- warning: real.cauchy_int_cast -> Real.cauchy_intCast is a dubious translation:
lean 3 declaration is
  forall (z : Int), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) z)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (HasLiftT.mk.{1, 1} Int (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CoeTCₓ.coe.{1, 1} Int (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Int.castCoe.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasIntCast.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))))) z)
but is expected to have type
  forall (z : Int), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (Int.cast.{0} Real Real.intCast z)) (Int.cast.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instIntCastCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) z)
Case conversion may be inaccurate. Consider using '#align real.cauchy_int_cast Real.cauchy_intCastₓ'. -/
theorem cauchy_intCast (z : ℤ) : (z : ℝ).cauchy = z :=
  rfl
#align real.cauchy_int_cast Real.cauchy_intCast

/- warning: real.cauchy_rat_cast -> Real.cauchy_ratCast is a dubious translation:
lean 3 declaration is
  forall (q : Rat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Real.cauchy ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) q)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (HasLiftT.mk.{1, 1} Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CoeTCₓ.coe.{1, 1} Rat (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (Rat.castCoe.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasRatCast.{0, 0} Rat Rat.linearOrderedField Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))))) q)
but is expected to have type
  forall (q : Rat), Eq.{1} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (Real.cauchy (RatCast.ratCast.{0} Real Real.ratCast q)) (RatCast.ratCast.{0} (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (CauSeq.Completion.instRatCastCauchyToRing.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat Rat.divisionRing (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) q)
Case conversion may be inaccurate. Consider using '#align real.cauchy_rat_cast Real.cauchy_ratCastₓ'. -/
theorem cauchy_ratCast (q : ℚ) : (q : ℝ).cauchy = q :=
  rfl
#align real.cauchy_rat_cast Real.cauchy_ratCast

instance : CommRing ℝ := by
  refine_struct
            { Real.hasNatCast,
              Real.hasIntCast with
              zero := (0 : ℝ)
              one := (1 : ℝ)
              mul := (· * ·)
              add := (· + ·)
              neg := @Neg.neg ℝ _
              sub := @Sub.sub ℝ _
              npow := @npowRec ℝ ⟨1⟩ ⟨(· * ·)⟩
              nsmul := @nsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩
              zsmul := @zsmulRec ℝ ⟨0⟩ ⟨(· + ·)⟩ ⟨@Neg.neg ℝ _⟩ } <;>
          repeat' rintro ⟨_⟩ <;>
        try rfl <;>
      simp [← of_cauchy_zero, ← of_cauchy_one, ← of_cauchy_add, ← of_cauchy_neg, ← of_cauchy_mul,
        fun n => show @coe ℕ ℝ ⟨_⟩ n = ⟨n⟩ from rfl, NatCast.natCast, IntCast.intCast] <;>
    first
      |apply
        add_assoc|apply
        add_comm|apply
        mul_assoc|apply mul_comm|apply left_distrib|apply right_distrib|apply sub_eq_add_neg|skip

/- warning: real.ring_equiv_Cauchy -> Real.ringEquivCauchy is a dubious translation:
lean 3 declaration is
  RingEquiv.{0, 0} Real (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) Real.hasMul Real.hasAdd (CauSeq.Completion.Cauchy.hasMul.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (CauSeq.Completion.Cauchy.hasAdd.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))
but is expected to have type
  RingEquiv.{0, 0} Real (CauSeq.Completion.Cauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) Real.instMulReal (CauSeq.Completion.instMulCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) Real.instAddReal (CauSeq.Completion.instAddCauchy.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))
Case conversion may be inaccurate. Consider using '#align real.ring_equiv_Cauchy Real.ringEquivCauchyₓ'. -/
/-- `real.equiv_Cauchy` as a ring equivalence. -/
@[simps]
def ringEquivCauchy : ℝ ≃+* CauSeq.Completion.Cauchy abs :=
  { equivCauchy with
    toFun := cauchy
    invFun := ofCauchy
    map_add' := cauchy_add
    map_mul' := cauchy_mul }
#align real.ring_equiv_Cauchy Real.ringEquivCauchy

/-! Extra instances to short-circuit type class resolution.

 These short-circuits have an additional property of ensuring that a computable path is found; if
 `field ℝ` is found first, then decaying it to these typeclasses would result in a `noncomputable`
 version of them. -/


instance : Ring ℝ := by infer_instance

instance : CommSemiring ℝ := by infer_instance

instance : Semiring ℝ := by infer_instance

instance : CommMonoidWithZero ℝ := by infer_instance

instance : MonoidWithZero ℝ := by infer_instance

instance : AddCommGroup ℝ := by infer_instance

instance : AddGroup ℝ := by infer_instance

instance : AddCommMonoid ℝ := by infer_instance

instance : AddMonoid ℝ := by infer_instance

instance : AddLeftCancelSemigroup ℝ := by infer_instance

instance : AddRightCancelSemigroup ℝ := by infer_instance

instance : AddCommSemigroup ℝ := by infer_instance

instance : AddSemigroup ℝ := by infer_instance

instance : CommMonoid ℝ := by infer_instance

instance : Monoid ℝ := by infer_instance

instance : CommSemigroup ℝ := by infer_instance

instance : Semigroup ℝ := by infer_instance

instance : Inhabited ℝ :=
  ⟨0⟩

/-- The real numbers are a `*`-ring, with the trivial `*`-structure. -/
instance : StarRing ℝ :=
  starRingOfComm

instance : TrivialStar ℝ :=
  ⟨fun _ => rfl⟩

/- warning: real.mk -> Real.mk is a dubious translation:
lean 3 declaration is
  (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) -> Real
but is expected to have type
  (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) -> Real
Case conversion may be inaccurate. Consider using '#align real.mk Real.mkₓ'. -/
/-- Make a real number from a Cauchy sequence of rationals (by taking the equivalence class). -/
def mk (x : CauSeq ℚ abs) : ℝ :=
  ⟨CauSeq.Completion.mk x⟩
#align real.mk Real.mk

/- warning: real.mk_eq -> Real.mk_eq is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Iff (Eq.{1} Real (Real.mk f) (Real.mk g)) (HasEquivₓ.Equiv.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (setoidHasEquiv.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) f g)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Iff (Eq.{1} Real (Real.mk f) (Real.mk g)) (HasEquiv.Equiv.{1, 0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (instHasEquiv.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) f g)
Case conversion may be inaccurate. Consider using '#align real.mk_eq Real.mk_eqₓ'. -/
theorem mk_eq {f g : CauSeq ℚ abs} : mk f = mk g ↔ f ≈ g :=
  ext_cauchy_iff.trans mk_eq
#align real.mk_eq Real.mk_eq

private irreducible_def lt : ℝ → ℝ → Prop
  | ⟨x⟩, ⟨y⟩ =>
    Quotient.liftOn₂ x y (· < ·) fun f₁ g₁ f₂ g₂ hf hg =>
      propext <|
        ⟨fun h => lt_of_eq_of_lt (Setoid.symm hf) (lt_of_lt_of_eq h hg), fun h =>
          lt_of_eq_of_lt hf (lt_of_lt_of_eq h (Setoid.symm hg))⟩
#align real.lt real.lt

instance : LT ℝ :=
  ⟨Lt⟩

/- warning: real.lt_cauchy -> Real.lt_cauchy is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Iff (LT.lt.{0} Real Real.hasLt (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) f)) (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) g))) (LT.lt.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasLt.{0} Rat Rat.linearOrderedField) f g)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Iff (LT.lt.{0} Real Real.instLTReal (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) f)) (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) g))) (LT.lt.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instLTCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) f g)
Case conversion may be inaccurate. Consider using '#align real.lt_cauchy Real.lt_cauchyₓ'. -/
theorem lt_cauchy {f g} : (⟨⟦f⟧⟩ : ℝ) < ⟨⟦g⟧⟩ ↔ f < g :=
  show Lt _ _ ↔ _ by rw [lt] <;> rfl
#align real.lt_cauchy Real.lt_cauchy

/- warning: real.mk_lt -> Real.mk_lt is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Iff (LT.lt.{0} Real Real.hasLt (Real.mk f) (Real.mk g)) (LT.lt.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasLt.{0} Rat Rat.linearOrderedField) f g)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Iff (LT.lt.{0} Real Real.instLTReal (Real.mk f) (Real.mk g)) (LT.lt.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instLTCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) f g)
Case conversion may be inaccurate. Consider using '#align real.mk_lt Real.mk_ltₓ'. -/
@[simp]
theorem mk_lt {f g : CauSeq ℚ abs} : mk f < mk g ↔ f < g :=
  lt_cauchy
#align real.mk_lt Real.mk_lt

/- warning: real.mk_zero -> Real.mk_zero is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.mk (OfNat.ofNat.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) 0 (OfNat.mk.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) 0 (Zero.zero.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasZero.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.mk (OfNat.ofNat.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) 0 (Zero.toOfNat0.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instZeroCauSeq.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.mk_zero Real.mk_zeroₓ'. -/
theorem mk_zero : mk 0 = 0 := by rw [← of_cauchy_zero] <;> rfl
#align real.mk_zero Real.mk_zero

/- warning: real.mk_one -> Real.mk_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.mk (OfNat.ofNat.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) 1 (OfNat.mk.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) 1 (One.one.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasOne.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)))))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  Eq.{1} Real (Real.mk (OfNat.ofNat.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) 1 (One.toOfNat1.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instOneCauSeq.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.mk_one Real.mk_oneₓ'. -/
theorem mk_one : mk 1 = 1 := by rw [← of_cauchy_one] <;> rfl
#align real.mk_one Real.mk_one

/- warning: real.mk_add -> Real.mk_add is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Eq.{1} Real (Real.mk (HAdd.hAdd.{0, 0, 0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (instHAdd.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasAdd.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) f g)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Real.mk f) (Real.mk g))
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Eq.{1} Real (Real.mk (HAdd.hAdd.{0, 0, 0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (instHAdd.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instAddCauSeq.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) f g)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Real.mk f) (Real.mk g))
Case conversion may be inaccurate. Consider using '#align real.mk_add Real.mk_addₓ'. -/
theorem mk_add {f g : CauSeq ℚ abs} : mk (f + g) = mk f + mk g := by simp [mk, ← of_cauchy_add]
#align real.mk_add Real.mk_add

/- warning: real.mk_mul -> Real.mk_mul is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Eq.{1} Real (Real.mk (HMul.hMul.{0, 0, 0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (instHMul.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasMul.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing))) f g)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.mk f) (Real.mk g))
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Eq.{1} Real (Real.mk (HMul.hMul.{0, 0, 0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (instHMul.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instMulCauSeq.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat))) f g)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.mk f) (Real.mk g))
Case conversion may be inaccurate. Consider using '#align real.mk_mul Real.mk_mulₓ'. -/
theorem mk_mul {f g : CauSeq ℚ abs} : mk (f * g) = mk f * mk g := by simp [mk, ← of_cauchy_mul]
#align real.mk_mul Real.mk_mul

/- warning: real.mk_neg -> Real.mk_neg is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Eq.{1} Real (Real.mk (Neg.neg.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasNeg.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) f)) (Neg.neg.{0} Real Real.hasNeg (Real.mk f))
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Eq.{1} Real (Real.mk (Neg.neg.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instNegCauSeq.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) f)) (Neg.neg.{0} Real Real.instNegReal (Real.mk f))
Case conversion may be inaccurate. Consider using '#align real.mk_neg Real.mk_negₓ'. -/
theorem mk_neg {f : CauSeq ℚ abs} : mk (-f) = -mk f := by simp [mk, ← of_cauchy_neg]
#align real.mk_neg Real.mk_neg

/- warning: real.mk_pos -> Real.mk_pos is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Iff (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.mk f)) (CauSeq.Pos.{0} Rat Rat.linearOrderedField f)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Iff (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.mk f)) (CauSeq.Pos.{0} Rat Rat.instLinearOrderedFieldRat f)
Case conversion may be inaccurate. Consider using '#align real.mk_pos Real.mk_posₓ'. -/
@[simp]
theorem mk_pos {f : CauSeq ℚ abs} : 0 < mk f ↔ Pos f := by
  rw [← mk_zero, mk_lt] <;> exact iff_of_eq (congr_arg Pos (sub_zero f))
#align real.mk_pos Real.mk_pos

private irreducible_def le (x y : ℝ) : Prop :=
  x < y ∨ x = y
#align real.le real.le

instance : LE ℝ :=
  ⟨Le⟩

private theorem le_def {x y : ℝ} : x ≤ y ↔ x < y ∨ x = y :=
  show Le _ _ ↔ _ by rw [le]
#align real.le_def real.le_def

/- warning: real.mk_le -> Real.mk_le is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {g : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, Iff (LE.le.{0} Real Real.hasLe (Real.mk f) (Real.mk g)) (LE.le.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasLe.{0} Rat Rat.linearOrderedField) f g)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {g : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, Iff (LE.le.{0} Real Real.instLEReal (Real.mk f) (Real.mk g)) (LE.le.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instLECauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) f g)
Case conversion may be inaccurate. Consider using '#align real.mk_le Real.mk_leₓ'. -/
@[simp]
theorem mk_le {f g : CauSeq ℚ abs} : mk f ≤ mk g ↔ f ≤ g := by simp [le_def, mk_eq] <;> rfl
#align real.mk_le Real.mk_le

/- warning: real.ind_mk -> Real.ind_mk is a dubious translation:
lean 3 declaration is
  forall {C : Real -> Prop} (x : Real), (forall (y : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))), C (Real.mk y)) -> (C x)
but is expected to have type
  forall {C : Real -> Prop} (x : Real), (forall (y : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))), C (Real.mk y)) -> (C x)
Case conversion may be inaccurate. Consider using '#align real.ind_mk Real.ind_mkₓ'. -/
@[elab_as_elim]
protected theorem ind_mk {C : Real → Prop} (x : Real) (h : ∀ y, C (mk y)) : C x :=
  by
  cases' x with x
  induction' x using Quot.inductionOn with x
  exact h x
#align real.ind_mk Real.ind_mk

/- warning: real.add_lt_add_iff_left -> Real.add_lt_add_iff_left is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real} (c : Real), Iff (LT.lt.{0} Real Real.hasLt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) c a) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) c b)) (LT.lt.{0} Real Real.hasLt a b)
but is expected to have type
  forall {a : Real} {b : Real} (c : Real), Iff (LT.lt.{0} Real Real.instLTReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) c a) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) c b)) (LT.lt.{0} Real Real.instLTReal a b)
Case conversion may be inaccurate. Consider using '#align real.add_lt_add_iff_left Real.add_lt_add_iff_leftₓ'. -/
theorem add_lt_add_iff_left {a b : ℝ} (c : ℝ) : c + a < c + b ↔ a < b :=
  by
  induction a using Real.ind_mk
  induction b using Real.ind_mk
  induction c using Real.ind_mk
  simp only [mk_lt, ← mk_add]
  show Pos _ ↔ Pos _; rw [add_sub_add_left_eq_sub]
#align real.add_lt_add_iff_left Real.add_lt_add_iff_left

instance : PartialOrder ℝ where
  le := (· ≤ ·)
  lt := (· < ·)
  lt_iff_le_not_le a b :=
    Real.ind_mk a fun a => Real.ind_mk b fun b => by simpa using lt_iff_le_not_le
  le_refl a := a.ind_mk (by intro a <;> rw [mk_le])
  le_trans a b c :=
    Real.ind_mk a fun a => Real.ind_mk b fun b => Real.ind_mk c fun c => by simpa using le_trans
  lt_iff_le_not_le a b :=
    Real.ind_mk a fun a => Real.ind_mk b fun b => by simpa using lt_iff_le_not_le
  le_antisymm a b :=
    Real.ind_mk a fun a => Real.ind_mk b fun b => by simpa [mk_eq] using @CauSeq.le_antisymm _ _ a b

instance : Preorder ℝ := by infer_instance

/- warning: real.rat_cast_lt -> Real.ratCast_lt is a dubious translation:
lean 3 declaration is
  forall {x : Rat} {y : Rat}, Iff (LT.lt.{0} Real Real.hasLt ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) x) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) y)) (LT.lt.{0} Rat Rat.hasLt x y)
but is expected to have type
  forall {x : Rat} {y : Rat}, Iff (LT.lt.{0} Real Real.instLTReal (RatCast.ratCast.{0} Real Real.ratCast x) (RatCast.ratCast.{0} Real Real.ratCast y)) (LT.lt.{0} Rat Rat.instLTRat_1 x y)
Case conversion may be inaccurate. Consider using '#align real.rat_cast_lt Real.ratCast_ltₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible[tactic.transparency.semireducible] } -/
theorem ratCast_lt {x y : ℚ} : (x : ℝ) < (y : ℝ) ↔ x < y :=
  by
  rw [mk_lt]
  exact const_lt
#align real.rat_cast_lt Real.ratCast_lt

/- warning: real.zero_lt_one -> Real.zero_lt_one is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align real.zero_lt_one Real.zero_lt_oneₓ'. -/
protected theorem zero_lt_one : (0 : ℝ) < 1 := by
  convert rat_cast_lt.2 zero_lt_one <;> simp [← of_cauchy_rat_cast, of_cauchy_one, of_cauchy_zero]
#align real.zero_lt_one Real.zero_lt_one

/- warning: real.fact_zero_lt_one -> Real.fact_zero_lt_one is a dubious translation:
lean 3 declaration is
  Fact (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Fact (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.fact_zero_lt_one Real.fact_zero_lt_oneₓ'. -/
protected theorem fact_zero_lt_one : Fact ((0 : ℝ) < 1) :=
  ⟨Real.zero_lt_one⟩
#align real.fact_zero_lt_one Real.fact_zero_lt_one

/- warning: real.mul_pos -> Real.mul_pos is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) b) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) a b))
but is expected to have type
  forall {a : Real} {b : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) b) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) a b))
Case conversion may be inaccurate. Consider using '#align real.mul_pos Real.mul_posₓ'. -/
protected theorem mul_pos {a b : ℝ} : 0 < a → 0 < b → 0 < a * b :=
  by
  induction' a using Real.ind_mk with a
  induction' b using Real.ind_mk with b
  simpa only [mk_lt, mk_pos, ← mk_mul] using CauSeq.mul_pos
#align real.mul_pos Real.mul_pos

instance : StrictOrderedCommRing ℝ :=
  { Real.commRing, Real.partialOrder,
    Real.semiring with
    exists_pair_ne := ⟨0, 1, Real.zero_lt_one.Ne⟩
    add_le_add_left := by
      simp only [le_iff_eq_or_lt]
      rintro a b ⟨rfl, h⟩
      · simp
      · exact fun c => Or.inr ((add_lt_add_iff_left c).2 ‹_›)
    zero_le_one := le_of_lt Real.zero_lt_one
    mul_pos := @Real.mul_pos }

instance : StrictOrderedRing ℝ :=
  inferInstance

instance : StrictOrderedCommSemiring ℝ :=
  inferInstance

instance : StrictOrderedSemiring ℝ :=
  inferInstance

instance : OrderedRing ℝ :=
  inferInstance

instance : OrderedSemiring ℝ :=
  inferInstance

instance : OrderedAddCommGroup ℝ :=
  inferInstance

instance : OrderedCancelAddCommMonoid ℝ :=
  inferInstance

instance : OrderedAddCommMonoid ℝ :=
  inferInstance

instance : Nontrivial ℝ :=
  inferInstance

private irreducible_def sup : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊔ ·) (fun x₁ x₂ hx y₁ y₂ hy => sup_equiv_sup hx hy) x y⟩
#align real.sup real.sup

instance : HasSup ℝ :=
  ⟨sup⟩

/- warning: real.of_cauchy_sup clashes with real.ofCauchy_sup -> Real.ofCauchy_sup
warning: real.of_cauchy_sup -> Real.ofCauchy_sup is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (b : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))), Eq.{1} Real (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (HasSup.sup.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasSup.{0} Rat Rat.linearOrderedField) a b))) (HasSup.sup.{0} Real Real.hasSup (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) a)) (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) b)))
but is expected to have type
  forall (a : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (b : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))), Eq.{1} Real (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (HasSup.sup.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instHasSupCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) a b))) (HasSup.sup.{0} Real Real.instHasSupReal (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) a)) (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) b)))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_sup Real.ofCauchy_supₓ'. -/
theorem ofCauchy_sup (a b) : (⟨⟦a ⊔ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊔ ⟨⟦b⟧⟩ :=
  show _ = sup _ _ by
    rw [sup]
    rfl
#align real.of_cauchy_sup Real.ofCauchy_sup

/- warning: real.mk_sup -> Real.mk_sup is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (b : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))), Eq.{1} Real (Real.mk (HasSup.sup.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasSup.{0} Rat Rat.linearOrderedField) a b)) (HasSup.sup.{0} Real Real.hasSup (Real.mk a) (Real.mk b))
but is expected to have type
  forall (a : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (b : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))), Eq.{1} Real (Real.mk (HasSup.sup.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instHasSupCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) a b)) (HasSup.sup.{0} Real Real.instHasSupReal (Real.mk a) (Real.mk b))
Case conversion may be inaccurate. Consider using '#align real.mk_sup Real.mk_supₓ'. -/
@[simp]
theorem mk_sup (a b) : (mk (a ⊔ b) : ℝ) = mk a ⊔ mk b :=
  ofCauchy_sup _ _
#align real.mk_sup Real.mk_sup

private irreducible_def inf : ℝ → ℝ → ℝ
  | ⟨x⟩, ⟨y⟩ => ⟨Quotient.map₂ (· ⊓ ·) (fun x₁ x₂ hx y₁ y₂ hy => inf_equiv_inf hx hy) x y⟩
#align real.inf real.inf

instance : HasInf ℝ :=
  ⟨inf⟩

/- warning: real.of_cauchy_inf clashes with real.ofCauchy_inf -> Real.ofCauchy_inf
warning: real.of_cauchy_inf -> Real.ofCauchy_inf is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (b : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))), Eq.{1} Real (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) (HasInf.inf.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasInf.{0} Rat Rat.linearOrderedField) a b))) (HasInf.inf.{0} Real Real.hasInf (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) a)) (Real.ofCauchy (Quotient.mk''.{1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.equiv.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.linearOrderedRing)) b)))
but is expected to have type
  forall (a : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (b : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))), Eq.{1} Real (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) (HasInf.inf.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instHasInfCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) a b))) (HasInf.inf.{0} Real Real.instHasInfReal (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) a)) (Real.ofCauchy (Quotient.mk.{1} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.equiv.{0, 0} Rat Rat Rat.instLinearOrderedFieldRat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Rat Rat.instLinearOrderedRingRat)) b)))
Case conversion may be inaccurate. Consider using '#align real.of_cauchy_inf Real.ofCauchy_infₓ'. -/
theorem ofCauchy_inf (a b) : (⟨⟦a ⊓ b⟧⟩ : ℝ) = ⟨⟦a⟧⟩ ⊓ ⟨⟦b⟧⟩ :=
  show _ = inf _ _ by
    rw [inf]
    rfl
#align real.of_cauchy_inf Real.ofCauchy_inf

/- warning: real.mk_inf -> Real.mk_inf is a dubious translation:
lean 3 declaration is
  forall (a : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (b : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))), Eq.{1} Real (Real.mk (HasInf.inf.{0} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (CauSeq.hasInf.{0} Rat Rat.linearOrderedField) a b)) (HasInf.inf.{0} Real Real.hasInf (Real.mk a) (Real.mk b))
but is expected to have type
  forall (a : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (b : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))), Eq.{1} Real (Real.mk (HasInf.inf.{0} (CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))) (CauSeq.instHasInfCauSeqToRingToDivisionRingToFieldAbsToHasAbsToNegToHasSupToSemilatticeSupToLatticeInstDistribLatticeToLinearOrderToLinearOrderedRingToLinearOrderedCommRing.{0} Rat Rat.instLinearOrderedFieldRat) a b)) (HasInf.inf.{0} Real Real.instHasInfReal (Real.mk a) (Real.mk b))
Case conversion may be inaccurate. Consider using '#align real.mk_inf Real.mk_infₓ'. -/
@[simp]
theorem mk_inf (a b) : (mk (a ⊓ b) : ℝ) = mk a ⊓ mk b :=
  ofCauchy_inf _ _
#align real.mk_inf Real.mk_inf

instance : DistribLattice ℝ :=
  { Real.partialOrder with
    sup := (· ⊔ ·)
    le := (· ≤ ·)
    le_sup_left := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b => by
          rw [← mk_sup, mk_le]
          exact CauSeq.le_sup_left
    le_sup_right := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b => by
          rw [← mk_sup, mk_le]
          exact CauSeq.le_sup_right
    sup_le := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b c =>
          Real.ind_mk c fun c => by
            simp_rw [← mk_sup, mk_le]
            exact CauSeq.sup_le
    inf := (· ⊓ ·)
    inf_le_left := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b => by
          rw [← mk_inf, mk_le]
          exact CauSeq.inf_le_left
    inf_le_right := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b => by
          rw [← mk_inf, mk_le]
          exact CauSeq.inf_le_right
    le_inf := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b c =>
          Real.ind_mk c fun c => by
            simp_rw [← mk_inf, mk_le]
            exact CauSeq.le_inf
    le_sup_inf := fun a =>
      Real.ind_mk a fun a b =>
        Real.ind_mk b fun b c =>
          Real.ind_mk c fun c =>
            Eq.le
              (by
                simp only [← mk_sup, ← mk_inf]
                exact congr_arg mk (CauSeq.sup_inf_distrib_left _ _ _).symm) }

-- Extra instances to short-circuit type class resolution
instance : Lattice ℝ :=
  inferInstance

instance : SemilatticeInf ℝ :=
  inferInstance

instance : SemilatticeSup ℝ :=
  inferInstance

open Classical

instance : IsTotal ℝ (· ≤ ·) :=
  ⟨fun a => Real.ind_mk a fun a b => Real.ind_mk b fun b => by simpa using le_total a b⟩

noncomputable instance : LinearOrder ℝ :=
  Lattice.toLinearOrder _

noncomputable instance : LinearOrderedCommRing ℝ :=
  { Real.nontrivial, Real.strictOrderedRing, Real.commRing, Real.linearOrder with }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedRing ℝ := by infer_instance

noncomputable instance : LinearOrderedSemiring ℝ := by infer_instance

instance : IsDomain ℝ :=
  { Real.nontrivial, Real.commRing, LinearOrderedRing.isDomain with }

noncomputable instance : LinearOrderedField ℝ :=
  { Real.linearOrderedCommRing with
    inv := Inv.inv
    mul_inv_cancel := by
      rintro ⟨a⟩ h
      rw [mul_comm]
      simp only [← of_cauchy_inv, ← of_cauchy_mul, ← of_cauchy_one, ← of_cauchy_zero, Ne.def] at *
      exact CauSeq.Completion.inv_mul_cancel h
    inv_zero := by simp [← of_cauchy_zero, ← of_cauchy_inv]
    ratCast := coe
    rat_cast_mk := fun n d hd h2 => by
      rw [← of_cauchy_rat_cast, Rat.cast_mk', of_cauchy_mul, of_cauchy_inv, of_cauchy_nat_cast,
        of_cauchy_int_cast] }

-- Extra instances to short-circuit type class resolution
noncomputable instance : LinearOrderedAddCommGroup ℝ := by infer_instance

#print Real.field /-
noncomputable instance field : Field ℝ := by infer_instance
#align real.field Real.field
-/

noncomputable instance : DivisionRing ℝ := by infer_instance

/- warning: real.decidable_lt -> Real.decidableLT is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Decidable (LT.lt.{0} Real Real.hasLt a b)
but is expected to have type
  forall (a : Real) (b : Real), Decidable (LT.lt.{0} Real Real.instLTReal a b)
Case conversion may be inaccurate. Consider using '#align real.decidable_lt Real.decidableLTₓ'. -/
noncomputable instance decidableLT (a b : ℝ) : Decidable (a < b) := by infer_instance
#align real.decidable_lt Real.decidableLT

/- warning: real.decidable_le -> Real.decidableLE is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Decidable (LE.le.{0} Real Real.hasLe a b)
but is expected to have type
  forall (a : Real) (b : Real), Decidable (LE.le.{0} Real Real.instLEReal a b)
Case conversion may be inaccurate. Consider using '#align real.decidable_le Real.decidableLEₓ'. -/
noncomputable instance decidableLE (a b : ℝ) : Decidable (a ≤ b) := by infer_instance
#align real.decidable_le Real.decidableLE

#print Real.decidableEq /-
noncomputable instance decidableEq (a b : ℝ) : Decidable (a = b) := by infer_instance
#align real.decidable_eq Real.decidableEq
-/

/-- Show an underlying cauchy sequence for real numbers.

The representative chosen is the one passed in the VM to `quot.mk`, so two cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance : Repr ℝ where repr r := "real.of_cauchy " ++ repr r.cauchy

/- warning: real.le_mk_of_forall_le -> Real.le_mk_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {x : Real} {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat Nat.hasLe j i) -> (LE.le.{0} Real Real.hasLe x ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) (coeFn.{1, 1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (fun (_x : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) => Nat -> Rat) (CauSeq.hasCoeToFun.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) f j))))) -> (LE.le.{0} Real Real.hasLe x (Real.mk f))
but is expected to have type
  forall {x : Real} {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat instLENat j i) -> (LE.le.{0} Real Real.instLEReal x (RatCast.ratCast.{0} Real Real.ratCast (Subtype.val.{1} (Nat -> Rat) (fun (f : Nat -> Rat) => IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) f j))))) -> (LE.le.{0} Real Real.instLEReal x (Real.mk f))
Case conversion may be inaccurate. Consider using '#align real.le_mk_of_forall_le Real.le_mk_of_forall_leₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { md := tactic.transparency.semireducible[tactic.transparency.semireducible] } -/
theorem le_mk_of_forall_le {f : CauSeq ℚ abs} : (∃ i, ∀ j ≥ i, x ≤ f j) → x ≤ mk f :=
  by
  intro h
  induction' x using Real.ind_mk with x
  apply le_of_not_lt
  rw [mk_lt]
  rintro ⟨K, K0, hK⟩
  obtain ⟨i, H⟩ := exists_forall_ge_and h (exists_forall_ge_and hK (f.cauchy₃ <| half_pos K0))
  apply not_lt_of_le (H _ le_rfl).1
  rw [mk_lt]
  refine' ⟨_, half_pos K0, i, fun j ij => _⟩
  have := add_le_add (H _ ij).2.1 (le_of_lt (abs_lt.1 <| (H _ le_rfl).2.2 _ ij).1)
  rwa [← sub_eq_add_neg, sub_self_div_two, sub_apply, sub_add_sub_cancel] at this
#align real.le_mk_of_forall_le Real.le_mk_of_forall_le

/- warning: real.mk_le_of_forall_le -> Real.mk_le_of_forall_le is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {x : Real}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat Nat.hasLe j i) -> (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) (coeFn.{1, 1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (fun (_x : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) => Nat -> Rat) (CauSeq.hasCoeToFun.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) f j)) x))) -> (LE.le.{0} Real Real.hasLe (Real.mk f) x)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {x : Real}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat instLENat j i) -> (LE.le.{0} Real Real.instLEReal (RatCast.ratCast.{0} Real Real.ratCast (Subtype.val.{1} (Nat -> Rat) (fun (f : Nat -> Rat) => IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) f j)) x))) -> (LE.le.{0} Real Real.instLEReal (Real.mk f) x)
Case conversion may be inaccurate. Consider using '#align real.mk_le_of_forall_le Real.mk_le_of_forall_leₓ'. -/
theorem mk_le_of_forall_le {f : CauSeq ℚ abs} {x : ℝ} (h : ∃ i, ∀ j ≥ i, (f j : ℝ) ≤ x) :
    mk f ≤ x := by
  cases' h with i H
  rw [← neg_le_neg_iff, ← mk_neg]
  exact le_mk_of_forall_le ⟨i, fun j ij => by simp [H _ ij]⟩
#align real.mk_le_of_forall_le Real.mk_le_of_forall_le

/- warning: real.mk_near_of_forall_near -> Real.mk_near_of_forall_near is a dubious translation:
lean 3 declaration is
  forall {f : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))} {x : Real} {ε : Real}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat Nat.hasLe j i) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) (coeFn.{1, 1} (CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) (fun (_x : CauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) => Nat -> Rat) (CauSeq.hasCoeToFun.{0, 0} Rat Rat Rat.linearOrderedField (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup))) f j)) x)) ε))) -> (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Real.mk f) x)) ε)
but is expected to have type
  forall {f : CauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat))} {x : Real} {ε : Real}, (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat instLENat j i) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (RatCast.ratCast.{0} Real Real.ratCast (Subtype.val.{1} (Nat -> Rat) (fun (f : Nat -> Rat) => IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) f j)) x)) ε))) -> (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Real.mk f) x)) ε)
Case conversion may be inaccurate. Consider using '#align real.mk_near_of_forall_near Real.mk_near_of_forall_nearₓ'. -/
theorem mk_near_of_forall_near {f : CauSeq ℚ abs} {x : ℝ} {ε : ℝ}
    (H : ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| ≤ ε) : |mk f - x| ≤ ε :=
  abs_sub_le_iff.2
    ⟨sub_le_iff_le_add'.2 <|
        mk_le_of_forall_le <|
          H.imp fun i h j ij => sub_le_iff_le_add'.1 (abs_sub_le_iff.1 <| h j ij).1,
      sub_le_comm.1 <|
        le_mk_of_forall_le <| H.imp fun i h j ij => sub_le_comm.1 (abs_sub_le_iff.1 <| h j ij).2⟩
#align real.mk_near_of_forall_near Real.mk_near_of_forall_near

instance : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, M0, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

/- warning: real.is_cau_seq_iff_lift -> Real.isCauSeq_iff_lift is a dubious translation:
lean 3 declaration is
  forall {f : Nat -> Rat}, Iff (IsCauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) f) (IsCauSeq.{0, 0} Real Real.linearOrderedField Real Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup)) (fun (i : Nat) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) (f i)))
but is expected to have type
  forall {f : Nat -> Rat}, Iff (IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) (IsCauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Real Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal)) (fun (i : Nat) => RatCast.ratCast.{0} Real Real.ratCast (f i)))
Case conversion may be inaccurate. Consider using '#align real.is_cau_seq_iff_lift Real.isCauSeq_iff_liftₓ'. -/
theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) :=
  ⟨fun H ε ε0 =>
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => lt_trans (by simpa using (@Rat.cast_lt ℝ _ _ _).2 (hi _ ij)) δε,
    fun H ε ε0 =>
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij =>
      (@Rat.cast_lt ℝ _ _ _).1 <| by simpa using hi _ ij⟩
#align real.is_cau_seq_iff_lift Real.isCauSeq_iff_lift

/- warning: real.of_near -> Real.of_near is a dubious translation:
lean 3 declaration is
  forall (f : Nat -> Rat) (x : Real), (forall (ε : Real), (GT.gt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat Nat.hasLe j i) -> (LT.lt.{0} Real Real.hasLt (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Rat Real (HasLiftT.mk.{1, 1} Rat Real (CoeTCₓ.coe.{1, 1} Rat Real (Rat.castCoe.{0} Real Real.hasRatCast))) (f j)) x)) ε)))) -> (Exists.{0} (IsCauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) f) (fun (h' : IsCauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) f) => Eq.{1} Real (Real.mk (Subtype.mk.{1} (Nat -> Rat) (fun (f : Nat -> Rat) => IsCauSeq.{0, 0} Rat Rat.linearOrderedField Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.hasNeg Rat.hasSup)) f) f h')) x))
but is expected to have type
  forall (f : Nat -> Rat) (x : Real), (forall (ε : Real), (GT.gt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Nat (fun (i : Nat) => forall (j : Nat), (GE.ge.{0} Nat instLENat j i) -> (LT.lt.{0} Real Real.instLTReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (RatCast.ratCast.{0} Real Real.ratCast (f j)) x)) ε)))) -> (Exists.{0} (IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) (fun (h' : IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) => Eq.{1} Real (Real.mk (Subtype.mk.{1} (Nat -> Rat) (fun (f : Nat -> Rat) => IsCauSeq.{0, 0} Rat Rat.instLinearOrderedFieldRat Rat (DivisionRing.toRing.{0} Rat Rat.divisionRing) (Abs.abs.{0} Rat (Neg.toHasAbs.{0} Rat Rat.instNegRat Rat.instHasSupRat)) f) f h')) x))
Case conversion may be inaccurate. Consider using '#align real.of_near Real.of_nearₓ'. -/
theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        eq_of_le_of_forall_le_of_dense (abs_nonneg _) fun ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun i h j ij => le_of_lt (h j ij)⟩
#align real.of_near Real.of_near

/- warning: real.exists_floor -> Real.exists_floor is a dubious translation:
lean 3 declaration is
  forall (x : Real), Exists.{1} Int (fun (ub : Int) => And (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) ub) x) (forall (z : Int), (LE.le.{0} Real Real.hasLe ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) z) x) -> (LE.le.{0} Int Int.hasLe z ub)))
but is expected to have type
  forall (x : Real), Exists.{1} Int (fun (ub : Int) => And (LE.le.{0} Real Real.instLEReal (Int.cast.{0} Real Real.intCast ub) x) (forall (z : Int), (LE.le.{0} Real Real.instLEReal (Int.cast.{0} Real Real.intCast z) x) -> (LE.le.{0} Int Int.instLEInt z ub)))
Case conversion may be inaccurate. Consider using '#align real.exists_floor Real.exists_floorₓ'. -/
theorem exists_floor (x : ℝ) : ∃ ub : ℤ, (ub : ℝ) ≤ x ∧ ∀ z : ℤ, (z : ℝ) ≤ x → z ≤ ub :=
  Int.exists_greatest_of_bdd
    (let ⟨n, hn⟩ := exists_int_gt x
    ⟨n, fun z h' => Int.cast_le.1 <| le_trans h' <| le_of_lt hn⟩)
    (let ⟨n, hn⟩ := exists_int_lt x
    ⟨n, le_of_lt hn⟩)
#align real.exists_floor Real.exists_floor

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (j k «expr ≥ » «expr⌈ ⌉₊»(«expr ⁻¹»(ε))) -/
#print Real.exists_isLUB /-
theorem exists_isLUB (S : Set ℝ) (hne : S.Nonempty) (hbdd : BddAbove S) : ∃ x, IsLUB S x :=
  by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ S, (m : ℝ) ≤ y * d } :=
    by
    cases' exists_int_gt U with k hk
    refine' fun d => ⟨k * d, fun z h => _⟩
    rcases h with ⟨y, yS, hy⟩
    refine' Int.cast_le.1 (hy.trans _)
    push_cast
    exact mul_le_mul_of_nonneg_right ((hU yS).trans hk.le) d.cast_nonneg
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ S, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ S, (y - (n : ℕ)⁻¹ : ℝ) < (f n / n : ℚ) :=
    by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp [-sub_eq_add_neg]
    rwa [lt_div_iff (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, _root_.inv_mul_cancel]
    exact ne_of_gt (Nat.cast_pos.2 n0)
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) :=
    by
    intro ε ε0
    suffices ∀ (j) (_ : j ≥ ⌈ε⁻¹⌉₊) (k) (_ : k ≥ ⌈ε⁻¹⌉₊), (f j / j - f k / k : ℚ) < ε
      by
      refine' ⟨_, fun j ij => abs_lt.2 ⟨_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine' lt_of_lt_of_le ((@Rat.cast_lt ℝ _ _ _).1 _) ((inv_le ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine' ⟨mk g, ⟨fun x xS => _, fun y h => _⟩⟩
  · refine' le_of_forall_ge_of_dense fun z xz => _
    cases' exists_nat_gt (x - z)⁻¹ with K hK
    refine' le_mk_of_forall_le ⟨K, fun n nK => _⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine' le_trans _ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  ·
    exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩
#align real.exists_is_lub Real.exists_isLUB
-/

noncomputable instance : SupSet ℝ :=
  ⟨fun S => if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0⟩

/- warning: real.Sup_def -> Real.supₛ_def is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), Eq.{1} Real (SupSet.supₛ.{0} Real Real.hasSup S) (dite.{1} Real (And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S)) (And.decidable (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S) (Classical.propDecidable (Set.Nonempty.{0} Real S)) (Classical.propDecidable (BddAbove.{0} Real Real.preorder S))) (fun (h : And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S)) => Classical.choose.{1} Real (fun (x : Real) => IsLUB.{0} Real Real.preorder S x) (Real.exists_isLUB S (And.left (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S) h) (And.right (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S) h))) (fun (h : Not (And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.preorder S))) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (S : Set.{0} Real), Eq.{1} Real (SupSet.supₛ.{0} Real Real.instSupSetReal S) (dite.{1} Real (And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S)) (instDecidableAnd (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S) (Classical.propDecidable (Set.Nonempty.{0} Real S)) (Classical.propDecidable (BddAbove.{0} Real Real.instPreorderReal S))) (fun (h : And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S)) => Classical.choose.{1} Real (fun (x : Real) => IsLUB.{0} Real Real.instPreorderReal S x) (Real.exists_isLUB S (And.left (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S) h) (And.right (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S) h))) (fun (h : Not (And (Set.Nonempty.{0} Real S) (BddAbove.{0} Real Real.instPreorderReal S))) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.Sup_def Real.supₛ_defₓ'. -/
theorem supₛ_def (S : Set ℝ) :
    supₛ S = if h : S.Nonempty ∧ BddAbove S then Classical.choose (exists_isLUB S h.1 h.2) else 0 :=
  rfl
#align real.Sup_def Real.supₛ_def

/- warning: real.is_lub_Sup -> Real.isLUB_supₛ is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (Set.Nonempty.{0} Real S) -> (BddAbove.{0} Real Real.preorder S) -> (IsLUB.{0} Real Real.preorder S (SupSet.supₛ.{0} Real Real.hasSup S))
but is expected to have type
  forall (S : Set.{0} Real), (Set.Nonempty.{0} Real S) -> (BddAbove.{0} Real Real.instPreorderReal S) -> (IsLUB.{0} Real Real.instPreorderReal S (SupSet.supₛ.{0} Real Real.instSupSetReal S))
Case conversion may be inaccurate. Consider using '#align real.is_lub_Sup Real.isLUB_supₛₓ'. -/
protected theorem isLUB_supₛ (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddAbove S) : IsLUB S (supₛ S) :=
  by
  simp only [Sup_def, dif_pos (And.intro h₁ h₂)]
  apply Classical.choose_spec
#align real.is_lub_Sup Real.isLUB_supₛ

noncomputable instance : InfSet ℝ :=
  ⟨fun S => -supₛ (-S)⟩

/- warning: real.Inf_def -> Real.infₛ_def is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), Eq.{1} Real (InfSet.infₛ.{0} Real Real.hasInf S) (Neg.neg.{0} Real Real.hasNeg (SupSet.supₛ.{0} Real Real.hasSup (Neg.neg.{0} (Set.{0} Real) (Set.hasNeg.{0} Real Real.hasNeg) S)))
but is expected to have type
  forall (S : Set.{0} Real), Eq.{1} Real (InfSet.infₛ.{0} Real Real.instInfSetReal S) (Neg.neg.{0} Real Real.instNegReal (SupSet.supₛ.{0} Real Real.instSupSetReal (Neg.neg.{0} (Set.{0} Real) (Set.neg.{0} Real Real.instNegReal) S)))
Case conversion may be inaccurate. Consider using '#align real.Inf_def Real.infₛ_defₓ'. -/
theorem infₛ_def (S : Set ℝ) : infₛ S = -supₛ (-S) :=
  rfl
#align real.Inf_def Real.infₛ_def

/- warning: real.is_glb_Inf -> Real.is_glb_infₛ is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (Set.Nonempty.{0} Real S) -> (BddBelow.{0} Real Real.preorder S) -> (IsGLB.{0} Real Real.preorder S (InfSet.infₛ.{0} Real Real.hasInf S))
but is expected to have type
  forall (S : Set.{0} Real), (Set.Nonempty.{0} Real S) -> (BddBelow.{0} Real Real.instPreorderReal S) -> (IsGLB.{0} Real Real.instPreorderReal S (InfSet.infₛ.{0} Real Real.instInfSetReal S))
Case conversion may be inaccurate. Consider using '#align real.is_glb_Inf Real.is_glb_infₛₓ'. -/
protected theorem is_glb_infₛ (S : Set ℝ) (h₁ : S.Nonempty) (h₂ : BddBelow S) : IsGLB S (infₛ S) :=
  by
  rw [Inf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_supₛ _ h₁.neg h₂.neg
#align real.is_glb_Inf Real.is_glb_infₛ

noncomputable instance : ConditionallyCompleteLinearOrder ℝ :=
  { Real.linearOrder, Real.lattice with
    sup := SupSet.supₛ
    inf := InfSet.infₛ
    le_cSup := fun s a hs ha => (Real.isLUB_supₛ s ⟨a, ha⟩ hs).1 ha
    cSup_le := fun s a hs ha => (Real.isLUB_supₛ s hs ⟨a, ha⟩).2 ha
    cInf_le := fun s a hs ha => (Real.is_glb_infₛ s ⟨a, ha⟩ hs).1 ha
    le_cInf := fun s a hs ha => (Real.is_glb_infₛ s hs ⟨a, ha⟩).2 ha }

/- warning: real.lt_Inf_add_pos -> Real.lt_infₛ_add_pos is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Set.Nonempty.{0} Real s) -> (forall {ε : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{1} Real (fun (a : Real) => Exists.{0} (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) a s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) a s) => LT.lt.{0} Real Real.hasLt a (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (InfSet.infₛ.{0} Real Real.hasInf s) ε)))))
but is expected to have type
  forall {s : Set.{0} Real}, (Set.Nonempty.{0} Real s) -> (forall {ε : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{1} Real (fun (a : Real) => And (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) a s) (LT.lt.{0} Real Real.instLTReal a (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (InfSet.infₛ.{0} Real Real.instInfSetReal s) ε)))))
Case conversion may be inaccurate. Consider using '#align real.lt_Inf_add_pos Real.lt_infₛ_add_posₓ'. -/
theorem lt_infₛ_add_pos {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : 0 < ε) :
    ∃ a ∈ s, a < infₛ s + ε :=
  exists_lt_of_cinfₛ_lt h <| lt_add_of_pos_right _ hε
#align real.lt_Inf_add_pos Real.lt_infₛ_add_pos

/- warning: real.add_neg_lt_Sup -> Real.add_neg_lt_supₛ is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Set.Nonempty.{0} Real s) -> (forall {ε : Real}, (LT.lt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (a : Real) => Exists.{0} (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) a s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) a s) => LT.lt.{0} Real Real.hasLt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (SupSet.supₛ.{0} Real Real.hasSup s) ε) a))))
but is expected to have type
  forall {s : Set.{0} Real}, (Set.Nonempty.{0} Real s) -> (forall {ε : Real}, (LT.lt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (a : Real) => And (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) a s) (LT.lt.{0} Real Real.instLTReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (SupSet.supₛ.{0} Real Real.instSupSetReal s) ε) a))))
Case conversion may be inaccurate. Consider using '#align real.add_neg_lt_Sup Real.add_neg_lt_supₛₓ'. -/
theorem add_neg_lt_supₛ {s : Set ℝ} (h : s.Nonempty) {ε : ℝ} (hε : ε < 0) :
    ∃ a ∈ s, supₛ s + ε < a :=
  exists_lt_of_lt_csupₛ h <| add_lt_iff_neg_left.2 hε
#align real.add_neg_lt_Sup Real.add_neg_lt_supₛ

/- warning: real.Inf_le_iff -> Real.infₛ_le_iff is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (BddBelow.{0} Real Real.preorder s) -> (Set.Nonempty.{0} Real s) -> (forall {a : Real}, Iff (LE.le.{0} Real Real.hasLe (InfSet.infₛ.{0} Real Real.hasInf s) a) (forall (ε : Real), (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) ε) -> (Exists.{1} Real (fun (x : Real) => Exists.{0} (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x s) => LT.lt.{0} Real Real.hasLt x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) a ε))))))
but is expected to have type
  forall {s : Set.{0} Real}, (BddBelow.{0} Real Real.instPreorderReal s) -> (Set.Nonempty.{0} Real s) -> (forall {a : Real}, Iff (LE.le.{0} Real Real.instLEReal (InfSet.infₛ.{0} Real Real.instInfSetReal s) a) (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) ε) -> (Exists.{1} Real (fun (x : Real) => And (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x s) (LT.lt.{0} Real Real.instLTReal x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) a ε))))))
Case conversion may be inaccurate. Consider using '#align real.Inf_le_iff Real.infₛ_le_iffₓ'. -/
theorem infₛ_le_iff {s : Set ℝ} (h : BddBelow s) (h' : s.Nonempty) {a : ℝ} :
    infₛ s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε :=
  by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_cinfₛ_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact cinfₛ_lt_of_lt h x_in hx
#align real.Inf_le_iff Real.infₛ_le_iff

/- warning: real.le_Sup_iff -> Real.le_supₛ_iff is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (BddAbove.{0} Real Real.preorder s) -> (Set.Nonempty.{0} Real s) -> (forall {a : Real}, Iff (LE.le.{0} Real Real.hasLe a (SupSet.supₛ.{0} Real Real.hasSup s)) (forall (ε : Real), (LT.lt.{0} Real Real.hasLt ε (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Exists.{1} Real (fun (x : Real) => Exists.{0} (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x s) (fun (H : Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x s) => LT.lt.{0} Real Real.hasLt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) a ε) x)))))
but is expected to have type
  forall {s : Set.{0} Real}, (BddAbove.{0} Real Real.instPreorderReal s) -> (Set.Nonempty.{0} Real s) -> (forall {a : Real}, Iff (LE.le.{0} Real Real.instLEReal a (SupSet.supₛ.{0} Real Real.instSupSetReal s)) (forall (ε : Real), (LT.lt.{0} Real Real.instLTReal ε (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Exists.{1} Real (fun (x : Real) => And (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x s) (LT.lt.{0} Real Real.instLTReal (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) a ε) x)))))
Case conversion may be inaccurate. Consider using '#align real.le_Sup_iff Real.le_supₛ_iffₓ'. -/
theorem le_supₛ_iff {s : Set ℝ} (h : BddAbove s) (h' : s.Nonempty) {a : ℝ} :
    a ≤ supₛ s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x :=
  by
  rw [le_iff_forall_pos_lt_add]
  refine' ⟨fun H ε ε_neg => _, fun H ε ε_pos => _⟩
  · exact exists_lt_of_lt_csupₛ h' (lt_sub_iff_add_lt.mp (H _ (neg_pos.mpr ε_neg)))
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    exact sub_lt_iff_lt_add.mp (lt_csupₛ_of_lt h x_in hx)
#align real.le_Sup_iff Real.le_supₛ_iff

/- warning: real.Sup_empty -> Real.supₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (SupSet.supₛ.{0} Real Real.hasSup (EmptyCollection.emptyCollection.{0} (Set.{0} Real) (Set.hasEmptyc.{0} Real))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (SupSet.supₛ.{0} Real Real.instSupSetReal (EmptyCollection.emptyCollection.{0} (Set.{0} Real) (Set.instEmptyCollectionSet.{0} Real))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.Sup_empty Real.supₛ_emptyₓ'. -/
@[simp]
theorem supₛ_empty : supₛ (∅ : Set ℝ) = 0 :=
  dif_neg <| by simp
#align real.Sup_empty Real.supₛ_empty

/- warning: real.csupr_empty -> Real.csupᵢ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} [_inst_1 : IsEmpty.{u1} α] (f : α -> Real), Eq.{1} Real (supᵢ.{0, u1} Real Real.hasSup α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Sort.{u1}} [_inst_1 : IsEmpty.{u1} α] (f : α -> Real), Eq.{1} Real (supᵢ.{0, u1} Real Real.instSupSetReal α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.csupr_empty Real.csupᵢ_emptyₓ'. -/
theorem csupᵢ_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨆ i, f i) = 0 :=
  by
  dsimp [supᵢ]
  convert Real.supₛ_empty
  rw [Set.range_eq_empty_iff]
  infer_instance
#align real.csupr_empty Real.csupᵢ_empty

/- warning: real.csupr_const_zero -> Real.csupᵢ_const_zero is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Eq.{1} Real (supᵢ.{0, u1} Real Real.hasSup α (fun (i : α) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Sort.{u1}}, Eq.{1} Real (supᵢ.{0, u1} Real Real.instSupSetReal α (fun (i : α) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.csupr_const_zero Real.csupᵢ_const_zeroₓ'. -/
@[simp]
theorem csupᵢ_const_zero {α : Sort _} : (⨆ i : α, (0 : ℝ)) = 0 :=
  by
  cases isEmpty_or_nonempty α
  · exact Real.csupᵢ_empty _
  · exact csupᵢ_const
#align real.csupr_const_zero Real.csupᵢ_const_zero

/- warning: real.Sup_of_not_bdd_above -> Real.supₛ_of_not_bddAbove is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Not (BddAbove.{0} Real Real.preorder s)) -> (Eq.{1} Real (SupSet.supₛ.{0} Real Real.hasSup s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {s : Set.{0} Real}, (Not (BddAbove.{0} Real Real.instPreorderReal s)) -> (Eq.{1} Real (SupSet.supₛ.{0} Real Real.instSupSetReal s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.Sup_of_not_bdd_above Real.supₛ_of_not_bddAboveₓ'. -/
theorem supₛ_of_not_bddAbove {s : Set ℝ} (hs : ¬BddAbove s) : supₛ s = 0 :=
  dif_neg fun h => hs h.2
#align real.Sup_of_not_bdd_above Real.supₛ_of_not_bddAbove

/- warning: real.supr_of_not_bdd_above -> Real.supᵢ_of_not_bddAbove is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {f : α -> Real}, (Not (BddAbove.{0} Real Real.preorder (Set.range.{0, u1} Real α f))) -> (Eq.{1} Real (supᵢ.{0, u1} Real Real.hasSup α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Sort.{u1}} {f : α -> Real}, (Not (BddAbove.{0} Real Real.instPreorderReal (Set.range.{0, u1} Real α f))) -> (Eq.{1} Real (supᵢ.{0, u1} Real Real.instSupSetReal α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.supr_of_not_bdd_above Real.supᵢ_of_not_bddAboveₓ'. -/
theorem supᵢ_of_not_bddAbove {α : Sort _} {f : α → ℝ} (hf : ¬BddAbove (Set.range f)) :
    (⨆ i, f i) = 0 :=
  supₛ_of_not_bddAbove hf
#align real.supr_of_not_bdd_above Real.supᵢ_of_not_bddAbove

/- warning: real.Sup_univ -> Real.supₛ_univ is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (SupSet.supₛ.{0} Real Real.hasSup (Set.univ.{0} Real)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (SupSet.supₛ.{0} Real Real.instSupSetReal (Set.univ.{0} Real)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.Sup_univ Real.supₛ_univₓ'. -/
theorem supₛ_univ : supₛ (@Set.univ ℝ) = 0 :=
  Real.supₛ_of_not_bddAbove fun ⟨x, h⟩ => not_le_of_lt (lt_add_one _) <| h (Set.mem_univ _)
#align real.Sup_univ Real.supₛ_univ

/- warning: real.Inf_empty -> Real.infₛ_empty is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (InfSet.infₛ.{0} Real Real.hasInf (EmptyCollection.emptyCollection.{0} (Set.{0} Real) (Set.hasEmptyc.{0} Real))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (InfSet.infₛ.{0} Real Real.instInfSetReal (EmptyCollection.emptyCollection.{0} (Set.{0} Real) (Set.instEmptyCollectionSet.{0} Real))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.Inf_empty Real.infₛ_emptyₓ'. -/
@[simp]
theorem infₛ_empty : infₛ (∅ : Set ℝ) = 0 := by simp [Inf_def, supₛ_empty]
#align real.Inf_empty Real.infₛ_empty

/- warning: real.cinfi_empty -> Real.cinfᵢ_empty is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} [_inst_1 : IsEmpty.{u1} α] (f : α -> Real), Eq.{1} Real (infᵢ.{0, u1} Real Real.hasInf α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Sort.{u1}} [_inst_1 : IsEmpty.{u1} α] (f : α -> Real), Eq.{1} Real (infᵢ.{0, u1} Real Real.instInfSetReal α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.cinfi_empty Real.cinfᵢ_emptyₓ'. -/
theorem cinfᵢ_empty {α : Sort _} [IsEmpty α] (f : α → ℝ) : (⨅ i, f i) = 0 := by
  rw [infᵢ_of_empty', infₛ_empty]
#align real.cinfi_empty Real.cinfᵢ_empty

/- warning: real.cinfi_const_zero -> Real.cinfᵢ_const_zero is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}}, Eq.{1} Real (infᵢ.{0, u1} Real Real.hasInf α (fun (i : α) => OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall {α : Sort.{u1}}, Eq.{1} Real (infᵢ.{0, u1} Real Real.instInfSetReal α (fun (i : α) => OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.cinfi_const_zero Real.cinfᵢ_const_zeroₓ'. -/
@[simp]
theorem cinfᵢ_const_zero {α : Sort _} : (⨅ i : α, (0 : ℝ)) = 0 :=
  by
  cases isEmpty_or_nonempty α
  · exact Real.cinfᵢ_empty _
  · exact cinfᵢ_const
#align real.cinfi_const_zero Real.cinfᵢ_const_zero

/- warning: real.Inf_of_not_bdd_below -> Real.infₛ_of_not_bddBelow is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real}, (Not (BddBelow.{0} Real Real.preorder s)) -> (Eq.{1} Real (InfSet.infₛ.{0} Real Real.hasInf s) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {s : Set.{0} Real}, (Not (BddBelow.{0} Real Real.instPreorderReal s)) -> (Eq.{1} Real (InfSet.infₛ.{0} Real Real.instInfSetReal s) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.Inf_of_not_bdd_below Real.infₛ_of_not_bddBelowₓ'. -/
theorem infₛ_of_not_bddBelow {s : Set ℝ} (hs : ¬BddBelow s) : infₛ s = 0 :=
  neg_eq_zero.2 <| Sup_of_not_bdd_above <| mt bddAbove_neg.1 hs
#align real.Inf_of_not_bdd_below Real.infₛ_of_not_bddBelow

/- warning: real.infi_of_not_bdd_below -> Real.infᵢ_of_not_bddBelow is a dubious translation:
lean 3 declaration is
  forall {α : Sort.{u1}} {f : α -> Real}, (Not (BddBelow.{0} Real Real.preorder (Set.range.{0, u1} Real α f))) -> (Eq.{1} Real (infᵢ.{0, u1} Real Real.hasInf α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {α : Sort.{u1}} {f : α -> Real}, (Not (BddBelow.{0} Real Real.instPreorderReal (Set.range.{0, u1} Real α f))) -> (Eq.{1} Real (infᵢ.{0, u1} Real Real.instInfSetReal α (fun (i : α) => f i)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.infi_of_not_bdd_below Real.infᵢ_of_not_bddBelowₓ'. -/
theorem infᵢ_of_not_bddBelow {α : Sort _} {f : α → ℝ} (hf : ¬BddBelow (Set.range f)) :
    (⨅ i, f i) = 0 :=
  infₛ_of_not_bddBelow hf
#align real.infi_of_not_bdd_below Real.infᵢ_of_not_bddBelow

/- warning: real.Sup_nonneg -> Real.supₛ_nonneg is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x S) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (SupSet.supₛ.{0} Real Real.hasSup S))
but is expected to have type
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x S) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (SupSet.supₛ.{0} Real Real.instSupSetReal S))
Case conversion may be inaccurate. Consider using '#align real.Sup_nonneg Real.supₛ_nonnegₓ'. -/
/--
As `0` is the default value for `real.Sup` of the empty set or sets which are not bounded above, it
suffices to show that `S` is bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem supₛ_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ supₛ S :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Sup_empty.ge
  · apply dite _ (fun h => le_csupₛ_of_le h hy <| hS y hy) fun h => (Sup_of_not_bdd_above h).ge
#align real.Sup_nonneg Real.supₛ_nonneg

/- warning: real.Sup_nonpos -> Real.supₛ_nonpos is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x S) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (LE.le.{0} Real Real.hasLe (SupSet.supₛ.{0} Real Real.hasSup S) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x S) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (LE.le.{0} Real Real.instLEReal (SupSet.supₛ.{0} Real Real.instSupSetReal S) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.Sup_nonpos Real.supₛ_nonposₓ'. -/
/-- As `0` is the default value for `real.Sup` of the empty set, it suffices to show that `S` is
bounded above by `0` to show that `Sup S ≤ 0`.
-/
theorem supₛ_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : supₛ S ≤ 0 :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Sup_empty.le, csupₛ_le hS₂ hS]
#align real.Sup_nonpos Real.supₛ_nonpos

/- warning: real.Inf_nonneg -> Real.infₛ_nonneg is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x S) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x)) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (InfSet.infₛ.{0} Real Real.hasInf S))
but is expected to have type
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x S) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x)) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (InfSet.infₛ.{0} Real Real.instInfSetReal S))
Case conversion may be inaccurate. Consider using '#align real.Inf_nonneg Real.infₛ_nonnegₓ'. -/
/-- As `0` is the default value for `real.Inf` of the empty set, it suffices to show that `S` is
bounded below by `0` to show that `0 ≤ Inf S`.
-/
theorem infₛ_nonneg (S : Set ℝ) (hS : ∀ x ∈ S, (0 : ℝ) ≤ x) : 0 ≤ infₛ S :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | hS₂)
  exacts[Inf_empty.ge, le_cinfₛ hS₂ hS]
#align real.Inf_nonneg Real.infₛ_nonneg

/- warning: real.Inf_nonpos -> Real.infₛ_nonpos is a dubious translation:
lean 3 declaration is
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x S) -> (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))) -> (LE.le.{0} Real Real.hasLe (InfSet.infₛ.{0} Real Real.hasInf S) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall (S : Set.{0} Real), (forall (x : Real), (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x S) -> (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))) -> (LE.le.{0} Real Real.instLEReal (InfSet.infₛ.{0} Real Real.instInfSetReal S) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.Inf_nonpos Real.infₛ_nonposₓ'. -/
/--
As `0` is the default value for `real.Inf` of the empty set or sets which are not bounded below, it
suffices to show that `S` is bounded above by `0` to show that `Inf S ≤ 0`.
-/
theorem infₛ_nonpos (S : Set ℝ) (hS : ∀ x ∈ S, x ≤ (0 : ℝ)) : infₛ S ≤ 0 :=
  by
  rcases S.eq_empty_or_nonempty with (rfl | ⟨y, hy⟩)
  · exact Inf_empty.le
  · apply dite _ (fun h => cinfₛ_le_of_le h hy <| hS y hy) fun h => (Inf_of_not_bdd_below h).le
#align real.Inf_nonpos Real.infₛ_nonpos

/- warning: real.Inf_le_Sup -> Real.infₛ_le_supₛ is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), (BddBelow.{0} Real Real.preorder s) -> (BddAbove.{0} Real Real.preorder s) -> (LE.le.{0} Real Real.hasLe (InfSet.infₛ.{0} Real Real.hasInf s) (SupSet.supₛ.{0} Real Real.hasSup s))
but is expected to have type
  forall (s : Set.{0} Real), (BddBelow.{0} Real Real.instPreorderReal s) -> (BddAbove.{0} Real Real.instPreorderReal s) -> (LE.le.{0} Real Real.instLEReal (InfSet.infₛ.{0} Real Real.instInfSetReal s) (SupSet.supₛ.{0} Real Real.instSupSetReal s))
Case conversion may be inaccurate. Consider using '#align real.Inf_le_Sup Real.infₛ_le_supₛₓ'. -/
theorem infₛ_le_supₛ (s : Set ℝ) (h₁ : BddBelow s) (h₂ : BddAbove s) : infₛ s ≤ supₛ s :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · rw [infₛ_empty, supₛ_empty]
  · exact cinfₛ_le_csupₛ h₁ h₂ hne
#align real.Inf_le_Sup Real.infₛ_le_supₛ

/- warning: real.cau_seq_converges -> Real.cauSeq_converges is a dubious translation:
lean 3 declaration is
  forall (f : CauSeq.{0, 0} Real Real.linearOrderedField Real Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup))), Exists.{1} Real (fun (x : Real) => HasEquivₓ.Equiv.{1} (CauSeq.{0, 0} Real Real.linearOrderedField Real Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup))) (setoidHasEquiv.{1} (CauSeq.{0, 0} Real Real.linearOrderedField Real Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup))) (CauSeq.equiv.{0, 0} Real Real Real.linearOrderedField Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Real Real.linearOrderedRing))) f (CauSeq.const.{0, 0} Real Real Real.linearOrderedField Real.ring (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Real Real.linearOrderedRing) x))
but is expected to have type
  forall (f : CauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Real Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal))), Exists.{1} Real (fun (x : Real) => HasEquiv.Equiv.{1, 0} (CauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Real Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal))) (instHasEquiv.{1} (CauSeq.{0, 0} Real Real.instLinearOrderedFieldReal Real Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal))) (CauSeq.equiv.{0, 0} Real Real Real.instLinearOrderedFieldReal Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Real Real.instLinearOrderedRingReal))) f (CauSeq.const.{0, 0} Real Real Real.instLinearOrderedFieldReal Real.instRingReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instHasSupReal)) (IsAbsoluteValue.abs_isAbsoluteValue.{0} Real Real.instLinearOrderedRingReal) x))
Case conversion may be inaccurate. Consider using '#align real.cau_seq_converges Real.cauSeq_convergesₓ'. -/
theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x :=
  by
  let S := { x : ℝ | const abs x < f }
  have lb : ∃ x, x ∈ S := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ S, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ S, y ≤ x := (exists_gt f).imp ub'
  refine' ⟨Sup S, ((lt_total _ _).resolve_left fun h => _).resolve_right fun h => _⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (csupₛ_le lb (ub' _ _)).not_lt (sub_lt_self _ (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine' (le_csupₛ ub _).not_lt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine' ⟨_, half_pos ε0, i, fun j ij => _⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij
#align real.cau_seq_converges Real.cauSeq_converges

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

end Real

