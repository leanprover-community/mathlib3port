/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.trigonometric.basic
! leanprover-community/mathlib commit 2c1d8ca2812b64f88992a5294ea3dba144755cd1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Exp

/-!
# Trigonometric functions

## Main definitions

This file contains the definition of `π`.

See also `analysis.special_functions.trigonometric.inverse` and
`analysis.special_functions.trigonometric.arctan` for the inverse trigonometric functions.

See also `analysis.special_functions.complex.arg` and
`analysis.special_functions.complex.log` for the complex argument function
and the complex logarithm.

## Main statements

Many basic inequalities on the real trigonometric functions are established.

The continuity of the usual trigonometric functions is proved.

Several facts about the real trigonometric functions have the proofs deferred to
`analysis.special_functions.trigonometric.complex`,
as they are most easily proved by appealing to the corresponding fact for
complex trigonometric functions.

See also `analysis.special_functions.trigonometric.chebyshev` for the multiple angle formulas
in terms of Chebyshev polynomials.

## Tags

sin, cos, tan, angle
-/


noncomputable section

open Classical Topology Filter

open Set Filter

namespace Complex

/- warning: complex.continuous_sin -> Complex.continuous_sin is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.sin
but is expected to have type
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.sin
Case conversion may be inaccurate. Consider using '#align complex.continuous_sin Complex.continuous_sinₓ'. -/
@[continuity]
theorem continuous_sin : Continuous sin :=
  by
  change Continuous fun z => (exp (-z * I) - exp (z * I)) * I / 2
  continuity
#align complex.continuous_sin Complex.continuous_sin

/- warning: complex.continuous_on_sin -> Complex.continuousOn_sin is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.sin s
but is expected to have type
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.sin s
Case conversion may be inaccurate. Consider using '#align complex.continuous_on_sin Complex.continuousOn_sinₓ'. -/
theorem continuousOn_sin {s : Set ℂ} : ContinuousOn sin s :=
  continuous_sin.ContinuousOn
#align complex.continuous_on_sin Complex.continuousOn_sin

/- warning: complex.continuous_cos -> Complex.continuous_cos is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.cos
but is expected to have type
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.cos
Case conversion may be inaccurate. Consider using '#align complex.continuous_cos Complex.continuous_cosₓ'. -/
@[continuity]
theorem continuous_cos : Continuous cos :=
  by
  change Continuous fun z => (exp (z * I) + exp (-z * I)) / 2
  continuity
#align complex.continuous_cos Complex.continuous_cos

/- warning: complex.continuous_on_cos -> Complex.continuousOn_cos is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.cos s
but is expected to have type
  forall {s : Set.{0} Complex}, ContinuousOn.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.cos s
Case conversion may be inaccurate. Consider using '#align complex.continuous_on_cos Complex.continuousOn_cosₓ'. -/
theorem continuousOn_cos {s : Set ℂ} : ContinuousOn cos s :=
  continuous_cos.ContinuousOn
#align complex.continuous_on_cos Complex.continuousOn_cos

/- warning: complex.continuous_sinh -> Complex.continuous_sinh is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.sinh
but is expected to have type
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.sinh
Case conversion may be inaccurate. Consider using '#align complex.continuous_sinh Complex.continuous_sinhₓ'. -/
@[continuity]
theorem continuous_sinh : Continuous sinh :=
  by
  change Continuous fun z => (exp z - exp (-z)) / 2
  continuity
#align complex.continuous_sinh Complex.continuous_sinh

/- warning: complex.continuous_cosh -> Complex.continuous_cosh is a dubious translation:
lean 3 declaration is
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.cosh
but is expected to have type
  Continuous.{0, 0} Complex Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.cosh
Case conversion may be inaccurate. Consider using '#align complex.continuous_cosh Complex.continuous_coshₓ'. -/
@[continuity]
theorem continuous_cosh : Continuous cosh :=
  by
  change Continuous fun z => (exp z + exp (-z)) / 2
  continuity
#align complex.continuous_cosh Complex.continuous_cosh

end Complex

namespace Real

variable {x y z : ℝ}

#print Real.continuous_sin /-
@[continuity]
theorem continuous_sin : Continuous sin :=
  Complex.continuous_re.comp (Complex.continuous_sin.comp Complex.continuous_ofReal)
#align real.continuous_sin Real.continuous_sin
-/

#print Real.continuousOn_sin /-
theorem continuousOn_sin {s} : ContinuousOn sin s :=
  continuous_sin.ContinuousOn
#align real.continuous_on_sin Real.continuousOn_sin
-/

#print Real.continuous_cos /-
@[continuity]
theorem continuous_cos : Continuous cos :=
  Complex.continuous_re.comp (Complex.continuous_cos.comp Complex.continuous_ofReal)
#align real.continuous_cos Real.continuous_cos
-/

#print Real.continuousOn_cos /-
theorem continuousOn_cos {s} : ContinuousOn cos s :=
  continuous_cos.ContinuousOn
#align real.continuous_on_cos Real.continuousOn_cos
-/

#print Real.continuous_sinh /-
@[continuity]
theorem continuous_sinh : Continuous sinh :=
  Complex.continuous_re.comp (Complex.continuous_sinh.comp Complex.continuous_ofReal)
#align real.continuous_sinh Real.continuous_sinh
-/

#print Real.continuous_cosh /-
@[continuity]
theorem continuous_cosh : Continuous cosh :=
  Complex.continuous_re.comp (Complex.continuous_cosh.comp Complex.continuous_ofReal)
#align real.continuous_cosh Real.continuous_cosh
-/

end Real

namespace Real

/- warning: real.exists_cos_eq_zero -> Real.exists_cos_eq_zero is a dubious translation:
lean 3 declaration is
  Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.image.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.image.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.exists_cos_eq_zero Real.exists_cos_eq_zeroₓ'. -/
theorem exists_cos_eq_zero : 0 ∈ cos '' Icc (1 : ℝ) 2 :=
  intermediate_value_Icc' (by norm_num) continuousOn_cos
    ⟨le_of_lt cos_two_neg, le_of_lt cos_one_pos⟩
#align real.exists_cos_eq_zero Real.exists_cos_eq_zero

#print Real.pi /-
/-- The number π = 3.14159265... Defined here using choice as twice a zero of cos in [1,2], from
which one can derive all its properties. For explicit bounds on π, see `data.real.pi.bounds`. -/
protected noncomputable def pi : ℝ :=
  2 * Classical.choose exists_cos_eq_zero
#align real.pi Real.pi
-/

-- mathport name: real.pi
scoped notation "π" => Real.pi

#print Real.cos_pi_div_two /-
@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 := by
  rw [Real.pi, mul_div_cancel_left _ (two_ne_zero' ℝ)] <;>
    exact (Classical.choose_spec exists_cos_eq_zero).2
#align real.cos_pi_div_two Real.cos_pi_div_two
-/

/- warning: real.one_le_pi_div_two -> Real.one_le_pi_div_two is a dubious translation:
lean 3 declaration is
  LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.one_le_pi_div_two Real.one_le_pi_div_twoₓ'. -/
theorem one_le_pi_div_two : (1 : ℝ) ≤ π / 2 := by
  rw [Real.pi, mul_div_cancel_left _ (two_ne_zero' ℝ)] <;>
    exact (Classical.choose_spec exists_cos_eq_zero).1.1
#align real.one_le_pi_div_two Real.one_le_pi_div_two

/- warning: real.pi_div_two_le_two -> Real.pi_div_two_le_two is a dubious translation:
lean 3 declaration is
  LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))
but is expected to have type
  LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align real.pi_div_two_le_two Real.pi_div_two_le_twoₓ'. -/
theorem pi_div_two_le_two : π / 2 ≤ 2 := by
  rw [Real.pi, mul_div_cancel_left _ (two_ne_zero' ℝ)] <;>
    exact (Classical.choose_spec exists_cos_eq_zero).1.2
#align real.pi_div_two_le_two Real.pi_div_two_le_two

/- warning: real.two_le_pi -> Real.two_le_pi is a dubious translation:
lean 3 declaration is
  LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi
but is expected to have type
  LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi
Case conversion may be inaccurate. Consider using '#align real.two_le_pi Real.two_le_piₓ'. -/
theorem two_le_pi : (2 : ℝ) ≤ π :=
  (div_le_div_right (show (0 : ℝ) < 2 by norm_num)).1
    (by rw [div_self (two_ne_zero' ℝ)] <;> exact one_le_pi_div_two)
#align real.two_le_pi Real.two_le_pi

/- warning: real.pi_le_four -> Real.pi_le_four is a dubious translation:
lean 3 declaration is
  LE.le.{0} Real Real.hasLe Real.pi (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  LE.le.{0} Real Real.instLEReal Real.pi (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))
Case conversion may be inaccurate. Consider using '#align real.pi_le_four Real.pi_le_fourₓ'. -/
theorem pi_le_four : π ≤ 4 :=
  (div_le_div_right (show (0 : ℝ) < 2 by norm_num)).1
    (calc
      π / 2 ≤ 2 := pi_div_two_le_two
      _ = 4 / 2 := by norm_num
      )
#align real.pi_le_four Real.pi_le_four

/- warning: real.pi_pos -> Real.pi_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi
Case conversion may be inaccurate. Consider using '#align real.pi_pos Real.pi_posₓ'. -/
theorem pi_pos : 0 < π :=
  lt_of_lt_of_le (by norm_num) two_le_pi
#align real.pi_pos Real.pi_pos

/- warning: real.pi_ne_zero -> Real.pi_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} Real Real.pi (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Ne.{1} Real Real.pi (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.pi_ne_zero Real.pi_ne_zeroₓ'. -/
theorem pi_ne_zero : π ≠ 0 :=
  ne_of_gt pi_pos
#align real.pi_ne_zero Real.pi_ne_zero

/- warning: real.pi_div_two_pos -> Real.pi_div_two_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.pi_div_two_pos Real.pi_div_two_posₓ'. -/
theorem pi_div_two_pos : 0 < π / 2 :=
  half_pos pi_pos
#align real.pi_div_two_pos Real.pi_div_two_pos

/- warning: real.two_pi_pos -> Real.two_pi_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi)
but is expected to have type
  LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi)
Case conversion may be inaccurate. Consider using '#align real.two_pi_pos Real.two_pi_posₓ'. -/
theorem two_pi_pos : 0 < 2 * π := by linarith [pi_pos]
#align real.two_pi_pos Real.two_pi_pos

end Real

namespace NNReal

open Real

open Real NNReal

#print NNReal.pi /-
/-- `π` considered as a nonnegative real. -/
noncomputable def pi : ℝ≥0 :=
  ⟨π, Real.pi_pos.le⟩
#align nnreal.pi NNReal.pi
-/

/- warning: nnreal.coe_real_pi -> NNReal.coe_real_pi is a dubious translation:
lean 3 declaration is
  Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) NNReal Real (HasLiftT.mk.{1, 1} NNReal Real (CoeTCₓ.coe.{1, 1} NNReal Real (coeBase.{1, 1} NNReal Real NNReal.Real.hasCoe))) NNReal.pi) Real.pi
but is expected to have type
  Eq.{1} Real (NNReal.toReal NNReal.pi) Real.pi
Case conversion may be inaccurate. Consider using '#align nnreal.coe_real_pi NNReal.coe_real_piₓ'. -/
@[simp]
theorem coe_real_pi : (pi : ℝ) = π :=
  rfl
#align nnreal.coe_real_pi NNReal.coe_real_pi

/- warning: nnreal.pi_pos -> NNReal.pi_pos is a dubious translation:
lean 3 declaration is
  LT.lt.{0} NNReal (Preorder.toHasLt.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))))) NNReal.pi
but is expected to have type
  LT.lt.{0} NNReal (Preorder.toLT.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero)) NNReal.pi
Case conversion may be inaccurate. Consider using '#align nnreal.pi_pos NNReal.pi_posₓ'. -/
theorem pi_pos : 0 < pi := by exact_mod_cast Real.pi_pos
#align nnreal.pi_pos NNReal.pi_pos

/- warning: nnreal.pi_ne_zero -> NNReal.pi_ne_zero is a dubious translation:
lean 3 declaration is
  Ne.{1} NNReal NNReal.pi (OfNat.ofNat.{0} NNReal 0 (OfNat.mk.{0} NNReal 0 (Zero.zero.{0} NNReal (MulZeroClass.toHasZero.{0} NNReal (NonUnitalNonAssocSemiring.toMulZeroClass.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))
but is expected to have type
  Ne.{1} NNReal NNReal.pi (OfNat.ofNat.{0} NNReal 0 (Zero.toOfNat0.{0} NNReal instNNRealZero))
Case conversion may be inaccurate. Consider using '#align nnreal.pi_ne_zero NNReal.pi_ne_zeroₓ'. -/
theorem pi_ne_zero : pi ≠ 0 :=
  pi_pos.ne'
#align nnreal.pi_ne_zero NNReal.pi_ne_zero

end NNReal

namespace Real

open Real

/- warning: real.sin_pi -> Real.sin_pi is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sin Real.pi) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  Eq.{1} Real (Real.sin Real.pi) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real.sin_pi Real.sin_piₓ'. -/
@[simp]
theorem sin_pi : sin π = 0 := by
  rw [← mul_div_cancel_left π (two_ne_zero' ℝ), two_mul, add_div, sin_add, cos_pi_div_two] <;> simp
#align real.sin_pi Real.sin_pi

/- warning: real.cos_pi -> Real.cos_pi is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.cos Real.pi) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Eq.{1} Real (Real.cos Real.pi) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.cos_pi Real.cos_piₓ'. -/
@[simp]
theorem cos_pi : cos π = -1 := by
  rw [← mul_div_cancel_left π (two_ne_zero' ℝ), mul_div_assoc, cos_two_mul, cos_pi_div_two] <;>
    simp [bit0, pow_add]
#align real.cos_pi Real.cos_pi

#print Real.sin_two_pi /-
@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]
#align real.sin_two_pi Real.sin_two_pi
-/

#print Real.cos_two_pi /-
@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]
#align real.cos_two_pi Real.cos_two_pi
-/

#print Real.sin_antiperiodic /-
theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]
#align real.sin_antiperiodic Real.sin_antiperiodic
-/

#print Real.sin_periodic /-
theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.Periodic
#align real.sin_periodic Real.sin_periodic
-/

#print Real.sin_add_pi /-
@[simp]
theorem sin_add_pi (x : ℝ) : sin (x + π) = -sin x :=
  sin_antiperiodic x
#align real.sin_add_pi Real.sin_add_pi
-/

#print Real.sin_add_two_pi /-
@[simp]
theorem sin_add_two_pi (x : ℝ) : sin (x + 2 * π) = sin x :=
  sin_periodic x
#align real.sin_add_two_pi Real.sin_add_two_pi
-/

#print Real.sin_sub_pi /-
@[simp]
theorem sin_sub_pi (x : ℝ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x
#align real.sin_sub_pi Real.sin_sub_pi
-/

#print Real.sin_sub_two_pi /-
@[simp]
theorem sin_sub_two_pi (x : ℝ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x
#align real.sin_sub_two_pi Real.sin_sub_two_pi
-/

#print Real.sin_pi_sub /-
@[simp]
theorem sin_pi_sub (x : ℝ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'
#align real.sin_pi_sub Real.sin_pi_sub
-/

#print Real.sin_two_pi_sub /-
@[simp]
theorem sin_two_pi_sub (x : ℝ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'
#align real.sin_two_pi_sub Real.sin_two_pi_sub
-/

#print Real.sin_nat_mul_pi /-
@[simp]
theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n
#align real.sin_nat_mul_pi Real.sin_nat_mul_pi
-/

#print Real.sin_int_mul_pi /-
@[simp]
theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n
#align real.sin_int_mul_pi Real.sin_int_mul_pi
-/

#print Real.sin_add_nat_mul_two_pi /-
@[simp]
theorem sin_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x
#align real.sin_add_nat_mul_two_pi Real.sin_add_nat_mul_two_pi
-/

#print Real.sin_add_int_mul_two_pi /-
@[simp]
theorem sin_add_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x
#align real.sin_add_int_mul_two_pi Real.sin_add_int_mul_two_pi
-/

#print Real.sin_sub_nat_mul_two_pi /-
@[simp]
theorem sin_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n
#align real.sin_sub_nat_mul_two_pi Real.sin_sub_nat_mul_two_pi
-/

#print Real.sin_sub_int_mul_two_pi /-
@[simp]
theorem sin_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n
#align real.sin_sub_int_mul_two_pi Real.sin_sub_int_mul_two_pi
-/

#print Real.sin_nat_mul_two_pi_sub /-
@[simp]
theorem sin_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n
#align real.sin_nat_mul_two_pi_sub Real.sin_nat_mul_two_pi_sub
-/

#print Real.sin_int_mul_two_pi_sub /-
@[simp]
theorem sin_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n
#align real.sin_int_mul_two_pi_sub Real.sin_int_mul_two_pi_sub
-/

#print Real.cos_antiperiodic /-
theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]
#align real.cos_antiperiodic Real.cos_antiperiodic
-/

#print Real.cos_periodic /-
theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.Periodic
#align real.cos_periodic Real.cos_periodic
-/

#print Real.cos_add_pi /-
@[simp]
theorem cos_add_pi (x : ℝ) : cos (x + π) = -cos x :=
  cos_antiperiodic x
#align real.cos_add_pi Real.cos_add_pi
-/

#print Real.cos_add_two_pi /-
@[simp]
theorem cos_add_two_pi (x : ℝ) : cos (x + 2 * π) = cos x :=
  cos_periodic x
#align real.cos_add_two_pi Real.cos_add_two_pi
-/

#print Real.cos_sub_pi /-
@[simp]
theorem cos_sub_pi (x : ℝ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x
#align real.cos_sub_pi Real.cos_sub_pi
-/

#print Real.cos_sub_two_pi /-
@[simp]
theorem cos_sub_two_pi (x : ℝ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x
#align real.cos_sub_two_pi Real.cos_sub_two_pi
-/

#print Real.cos_pi_sub /-
@[simp]
theorem cos_pi_sub (x : ℝ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'
#align real.cos_pi_sub Real.cos_pi_sub
-/

#print Real.cos_two_pi_sub /-
@[simp]
theorem cos_two_pi_sub (x : ℝ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'
#align real.cos_two_pi_sub Real.cos_two_pi_sub
-/

#print Real.cos_nat_mul_two_pi /-
@[simp]
theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero
#align real.cos_nat_mul_two_pi Real.cos_nat_mul_two_pi
-/

#print Real.cos_int_mul_two_pi /-
@[simp]
theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero
#align real.cos_int_mul_two_pi Real.cos_int_mul_two_pi
-/

#print Real.cos_add_nat_mul_two_pi /-
@[simp]
theorem cos_add_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x
#align real.cos_add_nat_mul_two_pi Real.cos_add_nat_mul_two_pi
-/

#print Real.cos_add_int_mul_two_pi /-
@[simp]
theorem cos_add_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x
#align real.cos_add_int_mul_two_pi Real.cos_add_int_mul_two_pi
-/

#print Real.cos_sub_nat_mul_two_pi /-
@[simp]
theorem cos_sub_nat_mul_two_pi (x : ℝ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n
#align real.cos_sub_nat_mul_two_pi Real.cos_sub_nat_mul_two_pi
-/

#print Real.cos_sub_int_mul_two_pi /-
@[simp]
theorem cos_sub_int_mul_two_pi (x : ℝ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n
#align real.cos_sub_int_mul_two_pi Real.cos_sub_int_mul_two_pi
-/

#print Real.cos_nat_mul_two_pi_sub /-
@[simp]
theorem cos_nat_mul_two_pi_sub (x : ℝ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n
#align real.cos_nat_mul_two_pi_sub Real.cos_nat_mul_two_pi_sub
-/

#print Real.cos_int_mul_two_pi_sub /-
@[simp]
theorem cos_int_mul_two_pi_sub (x : ℝ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n
#align real.cos_int_mul_two_pi_sub Real.cos_int_mul_two_pi_sub
-/

#print Real.cos_nat_mul_two_pi_add_pi /-
@[simp]
theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic
#align real.cos_nat_mul_two_pi_add_pi Real.cos_nat_mul_two_pi_add_pi
-/

#print Real.cos_int_mul_two_pi_add_pi /-
@[simp]
theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic
#align real.cos_int_mul_two_pi_add_pi Real.cos_int_mul_two_pi_add_pi
-/

#print Real.cos_nat_mul_two_pi_sub_pi /-
@[simp]
theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic
#align real.cos_nat_mul_two_pi_sub_pi Real.cos_nat_mul_two_pi_sub_pi
-/

#print Real.cos_int_mul_two_pi_sub_pi /-
@[simp]
theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic
#align real.cos_int_mul_two_pi_sub_pi Real.cos_int_mul_two_pi_sub_pi
-/

/- warning: real.sin_pos_of_pos_of_lt_pi -> Real.sin_pos_of_pos_of_lt_pi is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x Real.pi) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x Real.pi) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_pos_of_pos_of_lt_pi Real.sin_pos_of_pos_of_lt_piₓ'. -/
theorem sin_pos_of_pos_of_lt_pi {x : ℝ} (h0x : 0 < x) (hxp : x < π) : 0 < sin x :=
  if hx2 : x ≤ 2 then sin_pos_of_pos_of_le_two h0x hx2
  else
    have : (2 : ℝ) + 2 = 4 := rfl
    have : π - x ≤ 2 :=
      sub_le_iff_le_add.2 (le_trans pi_le_four (this ▸ add_le_add_left (le_of_not_ge hx2) _))
    sin_pi_sub x ▸ sin_pos_of_pos_of_le_two (sub_pos.2 hxp) this
#align real.sin_pos_of_pos_of_lt_pi Real.sin_pos_of_pos_of_lt_pi

/- warning: real.sin_pos_of_mem_Ioo -> Real.sin_pos_of_mem_Ioo is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi)) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi)) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_pos_of_mem_Ioo Real.sin_pos_of_mem_Iooₓ'. -/
theorem sin_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo 0 π) : 0 < sin x :=
  sin_pos_of_pos_of_lt_pi hx.1 hx.2
#align real.sin_pos_of_mem_Ioo Real.sin_pos_of_mem_Ioo

/- warning: real.sin_nonneg_of_mem_Icc -> Real.sin_nonneg_of_mem_Icc is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi)) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi)) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_nonneg_of_mem_Icc Real.sin_nonneg_of_mem_Iccₓ'. -/
theorem sin_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc 0 π) : 0 ≤ sin x :=
  by
  rw [← closure_Ioo pi_ne_zero.symm] at hx
  exact
    closure_lt_subset_le continuous_const continuous_sin
      (closure_mono (fun y => sin_pos_of_mem_Ioo) hx)
#align real.sin_nonneg_of_mem_Icc Real.sin_nonneg_of_mem_Icc

/- warning: real.sin_nonneg_of_nonneg_of_le_pi -> Real.sin_nonneg_of_nonneg_of_le_pi is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x Real.pi) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sin x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x Real.pi) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sin x))
Case conversion may be inaccurate. Consider using '#align real.sin_nonneg_of_nonneg_of_le_pi Real.sin_nonneg_of_nonneg_of_le_piₓ'. -/
theorem sin_nonneg_of_nonneg_of_le_pi {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π) : 0 ≤ sin x :=
  sin_nonneg_of_mem_Icc ⟨h0x, hxp⟩
#align real.sin_nonneg_of_nonneg_of_le_pi Real.sin_nonneg_of_nonneg_of_le_pi

/- warning: real.sin_neg_of_neg_of_neg_pi_lt -> Real.sin_neg_of_neg_of_neg_pi_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) x) -> (LT.lt.{0} Real Real.hasLt (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) x) -> (LT.lt.{0} Real Real.instLTReal (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.sin_neg_of_neg_of_neg_pi_lt Real.sin_neg_of_neg_of_neg_pi_ltₓ'. -/
theorem sin_neg_of_neg_of_neg_pi_lt {x : ℝ} (hx0 : x < 0) (hpx : -π < x) : sin x < 0 :=
  neg_pos.1 <| sin_neg x ▸ sin_pos_of_pos_of_lt_pi (neg_pos.2 hx0) (neg_lt.1 hpx)
#align real.sin_neg_of_neg_of_neg_pi_lt Real.sin_neg_of_neg_of_neg_pi_lt

/- warning: real.sin_nonpos_of_nonnpos_of_neg_pi_le -> Real.sin_nonpos_of_nonnpos_of_neg_pi_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg Real.pi) x) -> (LE.le.{0} Real Real.hasLe (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal Real.pi) x) -> (LE.le.{0} Real Real.instLEReal (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.sin_nonpos_of_nonnpos_of_neg_pi_le Real.sin_nonpos_of_nonnpos_of_neg_pi_leₓ'. -/
theorem sin_nonpos_of_nonnpos_of_neg_pi_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -π ≤ x) : sin x ≤ 0 :=
  neg_nonneg.1 <| sin_neg x ▸ sin_nonneg_of_nonneg_of_le_pi (neg_nonneg.2 hx0) (neg_le.1 hpx)
#align real.sin_nonpos_of_nonnpos_of_neg_pi_le Real.sin_nonpos_of_nonnpos_of_neg_pi_le

#print Real.sin_pi_div_two /-
@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  have : sin (π / 2) = 1 ∨ sin (π / 2) = -1 := by
    simpa [sq, mul_self_eq_one_iff] using sin_sq_add_cos_sq (π / 2)
  this.resolve_right fun h =>
    show ¬(0 : ℝ) < -1 by norm_num <|
      h ▸ sin_pos_of_pos_of_lt_pi pi_div_two_pos (half_lt_self pi_pos)
#align real.sin_pi_div_two Real.sin_pi_div_two
-/

#print Real.sin_add_pi_div_two /-
theorem sin_add_pi_div_two (x : ℝ) : sin (x + π / 2) = cos x := by simp [sin_add]
#align real.sin_add_pi_div_two Real.sin_add_pi_div_two
-/

#print Real.sin_sub_pi_div_two /-
theorem sin_sub_pi_div_two (x : ℝ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]
#align real.sin_sub_pi_div_two Real.sin_sub_pi_div_two
-/

#print Real.sin_pi_div_two_sub /-
theorem sin_pi_div_two_sub (x : ℝ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]
#align real.sin_pi_div_two_sub Real.sin_pi_div_two_sub
-/

#print Real.cos_add_pi_div_two /-
theorem cos_add_pi_div_two (x : ℝ) : cos (x + π / 2) = -sin x := by simp [cos_add]
#align real.cos_add_pi_div_two Real.cos_add_pi_div_two
-/

#print Real.cos_sub_pi_div_two /-
theorem cos_sub_pi_div_two (x : ℝ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]
#align real.cos_sub_pi_div_two Real.cos_sub_pi_div_two
-/

#print Real.cos_pi_div_two_sub /-
theorem cos_pi_div_two_sub (x : ℝ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]
#align real.cos_pi_div_two_sub Real.cos_pi_div_two_sub
-/

/- warning: real.cos_pos_of_mem_Ioo -> Real.cos_pos_of_mem_Ioo is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x))
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_pos_of_mem_Ioo Real.cos_pos_of_mem_Iooₓ'. -/
theorem cos_pos_of_mem_Ioo {x : ℝ} (hx : x ∈ Ioo (-(π / 2)) (π / 2)) : 0 < cos x :=
  sin_add_pi_div_two x ▸ sin_pos_of_mem_Ioo ⟨by linarith [hx.1], by linarith [hx.2]⟩
#align real.cos_pos_of_mem_Ioo Real.cos_pos_of_mem_Ioo

/- warning: real.cos_nonneg_of_mem_Icc -> Real.cos_nonneg_of_mem_Icc is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x))
but is expected to have type
  forall {x : Real}, (Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_nonneg_of_mem_Icc Real.cos_nonneg_of_mem_Iccₓ'. -/
theorem cos_nonneg_of_mem_Icc {x : ℝ} (hx : x ∈ Icc (-(π / 2)) (π / 2)) : 0 ≤ cos x :=
  sin_add_pi_div_two x ▸ sin_nonneg_of_mem_Icc ⟨by linarith [hx.1], by linarith [hx.2]⟩
#align real.cos_nonneg_of_mem_Icc Real.cos_nonneg_of_mem_Icc

/- warning: real.cos_nonneg_of_neg_pi_div_two_le_of_le -> Real.cos_nonneg_of_neg_pi_div_two_le_of_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.cos x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_nonneg_of_neg_pi_div_two_le_of_le Real.cos_nonneg_of_neg_pi_div_two_le_of_leₓ'. -/
theorem cos_nonneg_of_neg_pi_div_two_le_of_le {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    0 ≤ cos x :=
  cos_nonneg_of_mem_Icc ⟨hl, hu⟩
#align real.cos_nonneg_of_neg_pi_div_two_le_of_le Real.cos_nonneg_of_neg_pi_div_two_le_of_le

/- warning: real.cos_neg_of_pi_div_two_lt_of_lt -> Real.cos_neg_of_pi_div_two_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) x) -> (LT.lt.{0} Real Real.hasLt x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) Real.pi (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (LT.lt.{0} Real Real.hasLt (Real.cos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) x) -> (LT.lt.{0} Real Real.instLTReal x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) Real.pi (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (LT.lt.{0} Real Real.instLTReal (Real.cos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.cos_neg_of_pi_div_two_lt_of_lt Real.cos_neg_of_pi_div_two_lt_of_ltₓ'. -/
theorem cos_neg_of_pi_div_two_lt_of_lt {x : ℝ} (hx₁ : π / 2 < x) (hx₂ : x < π + π / 2) :
    cos x < 0 :=
  neg_pos.1 <| cos_pi_sub x ▸ cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
#align real.cos_neg_of_pi_div_two_lt_of_lt Real.cos_neg_of_pi_div_two_lt_of_lt

/- warning: real.cos_nonpos_of_pi_div_two_le_of_le -> Real.cos_nonpos_of_pi_div_two_le_of_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) x) -> (LE.le.{0} Real Real.hasLe x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) Real.pi (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (LE.le.{0} Real Real.hasLe (Real.cos x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) x) -> (LE.le.{0} Real Real.instLEReal x (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) Real.pi (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) -> (LE.le.{0} Real Real.instLEReal (Real.cos x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.cos_nonpos_of_pi_div_two_le_of_le Real.cos_nonpos_of_pi_div_two_le_of_leₓ'. -/
theorem cos_nonpos_of_pi_div_two_le_of_le {x : ℝ} (hx₁ : π / 2 ≤ x) (hx₂ : x ≤ π + π / 2) :
    cos x ≤ 0 :=
  neg_nonneg.1 <| cos_pi_sub x ▸ cos_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
#align real.cos_nonpos_of_pi_div_two_le_of_le Real.cos_nonpos_of_pi_div_two_le_of_le

/- warning: real.sin_eq_sqrt_one_sub_cos_sq -> Real.sin_eq_sqrt_one_sub_cos_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x Real.pi) -> (Eq.{1} Real (Real.sin x) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x Real.pi) -> (Eq.{1} Real (Real.sin x) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align real.sin_eq_sqrt_one_sub_cos_sq Real.sin_eq_sqrt_one_sub_cos_sqₓ'. -/
theorem sin_eq_sqrt_one_sub_cos_sq {x : ℝ} (hl : 0 ≤ x) (hu : x ≤ π) :
    sin x = sqrt (1 - cos x ^ 2) := by
  rw [← abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hl hu)]
#align real.sin_eq_sqrt_one_sub_cos_sq Real.sin_eq_sqrt_one_sub_cos_sq

/- warning: real.cos_eq_sqrt_one_sub_sin_sq -> Real.cos_eq_sqrt_one_sub_sin_sq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (Eq.{1} Real (Real.cos x) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (Eq.{1} Real (Real.cos x) (Real.sqrt (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align real.cos_eq_sqrt_one_sub_sin_sq Real.cos_eq_sqrt_one_sub_sin_sqₓ'. -/
theorem cos_eq_sqrt_one_sub_sin_sq {x : ℝ} (hl : -(π / 2) ≤ x) (hu : x ≤ π / 2) :
    cos x = sqrt (1 - sin x ^ 2) := by
  rw [← abs_cos_eq_sqrt_one_sub_sin_sq, abs_of_nonneg (cos_nonneg_of_mem_Icc ⟨hl, hu⟩)]
#align real.cos_eq_sqrt_one_sub_sin_sq Real.cos_eq_sqrt_one_sub_sin_sq

/- warning: real.sin_eq_zero_iff_of_lt_of_lt -> Real.sin_eq_zero_iff_of_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg Real.pi) x) -> (LT.lt.{0} Real Real.hasLt x Real.pi) -> (Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal Real.pi) x) -> (LT.lt.{0} Real Real.instLTReal x Real.pi) -> (Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.sin_eq_zero_iff_of_lt_of_lt Real.sin_eq_zero_iff_of_lt_of_ltₓ'. -/
theorem sin_eq_zero_iff_of_lt_of_lt {x : ℝ} (hx₁ : -π < x) (hx₂ : x < π) : sin x = 0 ↔ x = 0 :=
  ⟨fun h =>
    le_antisymm
      (le_of_not_gt fun h0 =>
        lt_irrefl (0 : ℝ) <|
          calc
            0 < sin x := sin_pos_of_pos_of_lt_pi h0 hx₂
            _ = 0 := h
            )
      (le_of_not_gt fun h0 =>
        lt_irrefl (0 : ℝ) <|
          calc
            0 = sin x := h.symm
            _ < 0 := sin_neg_of_neg_of_neg_pi_lt h0 hx₁
            ),
    fun h => by simp [h]⟩
#align real.sin_eq_zero_iff_of_lt_of_lt Real.sin_eq_zero_iff_of_lt_of_lt

/- warning: real.sin_eq_zero_iff -> Real.sin_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n) Real.pi) x))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast n) Real.pi) x))
Case conversion may be inaccurate. Consider using '#align real.sin_eq_zero_iff Real.sin_eq_zero_iffₓ'. -/
theorem sin_eq_zero_iff {x : ℝ} : sin x = 0 ↔ ∃ n : ℤ, (n : ℝ) * π = x :=
  ⟨fun h =>
    ⟨⌊x / π⌋,
      le_antisymm (sub_nonneg.1 (Int.sub_floor_div_mul_nonneg _ pi_pos))
        (sub_nonpos.1 <|
          le_of_not_gt fun h₃ =>
            (sin_pos_of_pos_of_lt_pi h₃ (Int.sub_floor_div_mul_lt _ pi_pos)).Ne
              (by simp [sub_eq_add_neg, sin_add, h, sin_int_mul_pi]))⟩,
    fun ⟨n, hn⟩ => hn ▸ sin_int_mul_pi _⟩
#align real.sin_eq_zero_iff Real.sin_eq_zero_iff

/- warning: real.sin_ne_zero_iff -> Real.sin_ne_zero_iff is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Ne.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (forall (n : Int), Ne.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n) Real.pi) x)
but is expected to have type
  forall {x : Real}, Iff (Ne.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (forall (n : Int), Ne.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast n) Real.pi) x)
Case conversion may be inaccurate. Consider using '#align real.sin_ne_zero_iff Real.sin_ne_zero_iffₓ'. -/
theorem sin_ne_zero_iff {x : ℝ} : sin x ≠ 0 ↔ ∀ n : ℤ, (n : ℝ) * π ≠ x := by
  rw [← not_exists, not_iff_not, sin_eq_zero_iff]
#align real.sin_ne_zero_iff Real.sin_ne_zero_iff

/- warning: real.sin_eq_zero_iff_cos_eq -> Real.sin_eq_zero_iff_cos_eq is a dubious translation:
lean 3 declaration is
  forall {x : Real}, Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Or (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real (Real.cos x) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  forall {x : Real}, Iff (Eq.{1} Real (Real.sin x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Or (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real (Real.cos x) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))
Case conversion may be inaccurate. Consider using '#align real.sin_eq_zero_iff_cos_eq Real.sin_eq_zero_iff_cos_eqₓ'. -/
theorem sin_eq_zero_iff_cos_eq {x : ℝ} : sin x = 0 ↔ cos x = 1 ∨ cos x = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq x, sq, sq, ← sub_eq_iff_eq_add, sub_self] <;>
    exact ⟨fun h => by rw [h, MulZeroClass.mul_zero], eq_zero_of_mul_self_eq_zero ∘ Eq.symm⟩
#align real.sin_eq_zero_iff_cos_eq Real.sin_eq_zero_iff_cos_eq

/- warning: real.cos_eq_one_iff -> Real.cos_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall (x : Real), Iff (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Real (HasLiftT.mk.{1, 1} Int Real (CoeTCₓ.coe.{1, 1} Int Real (Int.castCoe.{0} Real Real.hasIntCast))) n) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi)) x))
but is expected to have type
  forall (x : Real), Iff (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Exists.{1} Int (fun (n : Int) => Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Int.cast.{0} Real Real.intCast n) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi)) x))
Case conversion may be inaccurate. Consider using '#align real.cos_eq_one_iff Real.cos_eq_one_iffₓ'. -/
theorem cos_eq_one_iff (x : ℝ) : cos x = 1 ↔ ∃ n : ℤ, (n : ℝ) * (2 * π) = x :=
  ⟨fun h =>
    let ⟨n, hn⟩ := sin_eq_zero_iff.1 (sin_eq_zero_iff_cos_eq.2 (Or.inl h))
    ⟨n / 2,
      (Int.emod_two_eq_zero_or_one n).elim
        (fun hn0 => by
          rwa [← mul_assoc, ← @Int.cast_two ℝ, ← Int.cast_mul,
            Int.ediv_mul_cancel ((Int.dvd_iff_emod_eq_zero _ _).2 hn0)])
        fun hn1 => by
        rw [← Int.emod_add_ediv n 2, hn1, Int.cast_add, Int.cast_one, add_mul, one_mul, add_comm,
              mul_comm (2 : ℤ), Int.cast_mul, mul_assoc, Int.cast_two] at hn <;>
            rw [← hn, cos_int_mul_two_pi_add_pi] at h <;>
          exact absurd h (by norm_num)⟩,
    fun ⟨n, hn⟩ => hn ▸ cos_int_mul_two_pi _⟩
#align real.cos_eq_one_iff Real.cos_eq_one_iff

/- warning: real.cos_eq_one_iff_of_lt_of_lt -> Real.cos_eq_one_iff_of_lt_of_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi)) x) -> (LT.lt.{0} Real Real.hasLt x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) Real.pi)) -> (Iff (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi)) x) -> (LT.lt.{0} Real Real.instLTReal x (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) Real.pi)) -> (Iff (Eq.{1} Real (Real.cos x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Eq.{1} Real x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.cos_eq_one_iff_of_lt_of_lt Real.cos_eq_one_iff_of_lt_of_ltₓ'. -/
theorem cos_eq_one_iff_of_lt_of_lt {x : ℝ} (hx₁ : -(2 * π) < x) (hx₂ : x < 2 * π) :
    cos x = 1 ↔ x = 0 :=
  ⟨fun h => by
    rcases(cos_eq_one_iff _).1 h with ⟨n, rfl⟩
    rw [mul_lt_iff_lt_one_left two_pi_pos] at hx₂
    rw [neg_lt, neg_mul_eq_neg_mul, mul_lt_iff_lt_one_left two_pi_pos] at hx₁
    norm_cast  at hx₁ hx₂
    obtain rfl : n = 0 := le_antisymm (by linarith) (by linarith)
    simp, fun h => by simp [h]⟩
#align real.cos_eq_one_iff_of_lt_of_lt Real.cos_eq_one_iff_of_lt_of_lt

/- warning: real.cos_lt_cos_of_nonneg_of_le_pi_div_two -> Real.cos_lt_cos_of_nonneg_of_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.cos y) (Real.cos x))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.cos y) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_lt_cos_of_nonneg_of_le_pi_div_two Real.cos_lt_cos_of_nonneg_of_le_pi_div_twoₓ'. -/
theorem cos_lt_cos_of_nonneg_of_le_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : cos y < cos x :=
  by
  rw [← sub_lt_zero, cos_sub_cos]
  have : 0 < sin ((y + x) / 2) := by refine' sin_pos_of_pos_of_lt_pi _ _ <;> linarith
  have : 0 < sin ((y - x) / 2) := by refine' sin_pos_of_pos_of_lt_pi _ _ <;> linarith
  nlinarith
#align real.cos_lt_cos_of_nonneg_of_le_pi_div_two Real.cos_lt_cos_of_nonneg_of_le_pi_div_two

/- warning: real.cos_lt_cos_of_nonneg_of_le_pi -> Real.cos_lt_cos_of_nonneg_of_le_pi is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe y Real.pi) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.cos y) (Real.cos x))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal y Real.pi) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.cos y) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_lt_cos_of_nonneg_of_le_pi Real.cos_lt_cos_of_nonneg_of_le_piₓ'. -/
theorem cos_lt_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x < y) :
    cos y < cos x :=
  match (le_total x (π / 2) : x ≤ π / 2 ∨ π / 2 ≤ x), le_total y (π / 2) with
  | Or.inl hx, Or.inl hy => cos_lt_cos_of_nonneg_of_le_pi_div_two hx₁ hy hxy
  | Or.inl hx, Or.inr hy =>
    (lt_or_eq_of_le hx).elim
      (fun hx =>
        calc
          cos y ≤ 0 := cos_nonpos_of_pi_div_two_le_of_le hy (by linarith [pi_pos])
          _ < cos x := cos_pos_of_mem_Ioo ⟨by linarith, hx⟩
          )
      fun hx =>
      calc
        cos y < 0 := cos_neg_of_pi_div_two_lt_of_lt (by linarith) (by linarith [pi_pos])
        _ = cos x := by rw [hx, cos_pi_div_two]
        
  | Or.inr hx, Or.inl hy => by linarith
  | Or.inr hx, Or.inr hy =>
    neg_lt_neg_iff.1
      (by
        rw [← cos_pi_sub, ← cos_pi_sub] <;> apply cos_lt_cos_of_nonneg_of_le_pi_div_two <;>
          linarith)
#align real.cos_lt_cos_of_nonneg_of_le_pi Real.cos_lt_cos_of_nonneg_of_le_pi

/- warning: real.strict_anti_on_cos -> Real.strictAntiOn_cos is a dubious translation:
lean 3 declaration is
  StrictAntiOn.{0, 0} Real Real Real.preorder Real.preorder Real.cos (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi)
but is expected to have type
  StrictAntiOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.cos (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi)
Case conversion may be inaccurate. Consider using '#align real.strict_anti_on_cos Real.strictAntiOn_cosₓ'. -/
theorem strictAntiOn_cos : StrictAntiOn cos (Icc 0 π) := fun x hx y hy hxy =>
  cos_lt_cos_of_nonneg_of_le_pi hx.1 hy.2 hxy
#align real.strict_anti_on_cos Real.strictAntiOn_cos

/- warning: real.cos_le_cos_of_nonneg_of_le_pi -> Real.cos_le_cos_of_nonneg_of_le_pi is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe y Real.pi) -> (LE.le.{0} Real Real.hasLe x y) -> (LE.le.{0} Real Real.hasLe (Real.cos y) (Real.cos x))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal y Real.pi) -> (LE.le.{0} Real Real.instLEReal x y) -> (LE.le.{0} Real Real.instLEReal (Real.cos y) (Real.cos x))
Case conversion may be inaccurate. Consider using '#align real.cos_le_cos_of_nonneg_of_le_pi Real.cos_le_cos_of_nonneg_of_le_piₓ'. -/
theorem cos_le_cos_of_nonneg_of_le_pi {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y ≤ π) (hxy : x ≤ y) :
    cos y ≤ cos x :=
  (strictAntiOn_cos.le_iff_le ⟨hx₁.trans hxy, hy₂⟩ ⟨hx₁, hxy.trans hy₂⟩).2 hxy
#align real.cos_le_cos_of_nonneg_of_le_pi Real.cos_le_cos_of_nonneg_of_le_pi

/- warning: real.sin_lt_sin_of_lt_of_le_pi_div_two -> Real.sin_lt_sin_of_lt_of_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.sin x) (Real.sin y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.sin x) (Real.sin y))
Case conversion may be inaccurate. Consider using '#align real.sin_lt_sin_of_lt_of_le_pi_div_two Real.sin_lt_sin_of_lt_of_le_pi_div_twoₓ'. -/
theorem sin_lt_sin_of_lt_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x < y) : sin x < sin y := by
  rw [← cos_sub_pi_div_two, ← cos_sub_pi_div_two, ← cos_neg (x - _), ← cos_neg (y - _)] <;>
      apply cos_lt_cos_of_nonneg_of_le_pi <;>
    linarith
#align real.sin_lt_sin_of_lt_of_le_pi_div_two Real.sin_lt_sin_of_lt_of_le_pi_div_two

/- warning: real.strict_mono_on_sin -> Real.strictMonoOn_sin is a dubious translation:
lean 3 declaration is
  StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder Real.sin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.sin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_sin Real.strictMonoOn_sinₓ'. -/
theorem strictMonoOn_sin : StrictMonoOn sin (Icc (-(π / 2)) (π / 2)) := fun x hx y hy hxy =>
  sin_lt_sin_of_lt_of_le_pi_div_two hx.1 hy.2 hxy
#align real.strict_mono_on_sin Real.strictMonoOn_sin

/- warning: real.sin_le_sin_of_le_of_le_pi_div_two -> Real.sin_le_sin_of_le_of_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LE.le.{0} Real Real.hasLe x y) -> (LE.le.{0} Real Real.hasLe (Real.sin x) (Real.sin y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LE.le.{0} Real Real.instLEReal x y) -> (LE.le.{0} Real Real.instLEReal (Real.sin x) (Real.sin y))
Case conversion may be inaccurate. Consider using '#align real.sin_le_sin_of_le_of_le_pi_div_two Real.sin_le_sin_of_le_of_le_pi_div_twoₓ'. -/
theorem sin_le_sin_of_le_of_le_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) ≤ x) (hy₂ : y ≤ π / 2)
    (hxy : x ≤ y) : sin x ≤ sin y :=
  (strictMonoOn_sin.le_iff_le ⟨hx₁, hxy.trans hy₂⟩ ⟨hx₁.trans hxy, hy₂⟩).2 hxy
#align real.sin_le_sin_of_le_of_le_pi_div_two Real.sin_le_sin_of_le_of_le_pi_div_two

/- warning: real.inj_on_sin -> Real.injOn_sin is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.inj_on_sin Real.injOn_sinₓ'. -/
theorem injOn_sin : InjOn sin (Icc (-(π / 2)) (π / 2)) :=
  strictMonoOn_sin.InjOn
#align real.inj_on_sin Real.injOn_sin

/- warning: real.inj_on_cos -> Real.injOn_cos is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi)
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi)
Case conversion may be inaccurate. Consider using '#align real.inj_on_cos Real.injOn_cosₓ'. -/
theorem injOn_cos : InjOn cos (Icc 0 π) :=
  strictAntiOn_cos.InjOn
#align real.inj_on_cos Real.injOn_cos

/- warning: real.surj_on_sin -> Real.surjOn_sin is a dubious translation:
lean 3 declaration is
  Set.SurjOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.SurjOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.surj_on_sin Real.surjOn_sinₓ'. -/
theorem surjOn_sin : SurjOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) := by
  simpa only [sin_neg, sin_pi_div_two] using
    intermediate_value_Icc (neg_le_self pi_div_two_pos.le) continuous_sin.continuous_on
#align real.surj_on_sin Real.surjOn_sin

/- warning: real.surj_on_cos -> Real.surjOn_cos is a dubious translation:
lean 3 declaration is
  Set.SurjOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.SurjOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.surj_on_cos Real.surjOn_cosₓ'. -/
theorem surjOn_cos : SurjOn cos (Icc 0 π) (Icc (-1) 1) := by
  simpa only [cos_zero, cos_pi] using intermediate_value_Icc' pi_pos.le continuous_cos.continuous_on
#align real.surj_on_cos Real.surjOn_cos

/- warning: real.sin_mem_Icc -> Real.sin_mem_Icc is a dubious translation:
lean 3 declaration is
  forall (x : Real), Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (Real.sin x) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (x : Real), Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Real.sin x) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.sin_mem_Icc Real.sin_mem_Iccₓ'. -/
theorem sin_mem_Icc (x : ℝ) : sin x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_sin x, sin_le_one x⟩
#align real.sin_mem_Icc Real.sin_mem_Icc

/- warning: real.cos_mem_Icc -> Real.cos_mem_Icc is a dubious translation:
lean 3 declaration is
  forall (x : Real), Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) (Real.cos x) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (x : Real), Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) (Real.cos x) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.cos_mem_Icc Real.cos_mem_Iccₓ'. -/
theorem cos_mem_Icc (x : ℝ) : cos x ∈ Icc (-1 : ℝ) 1 :=
  ⟨neg_one_le_cos x, cos_le_one x⟩
#align real.cos_mem_Icc Real.cos_mem_Icc

/- warning: real.maps_to_sin -> Real.mapsTo_sin is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Set.MapsTo.{0, 0} Real Real Real.sin s (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (s : Set.{0} Real), Set.MapsTo.{0, 0} Real Real Real.sin s (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.maps_to_sin Real.mapsTo_sinₓ'. -/
theorem mapsTo_sin (s : Set ℝ) : MapsTo sin s (Icc (-1 : ℝ) 1) := fun x _ => sin_mem_Icc x
#align real.maps_to_sin Real.mapsTo_sin

/- warning: real.maps_to_cos -> Real.mapsTo_cos is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Set.MapsTo.{0, 0} Real Real Real.cos s (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (s : Set.{0} Real), Set.MapsTo.{0, 0} Real Real Real.cos s (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.maps_to_cos Real.mapsTo_cosₓ'. -/
theorem mapsTo_cos (s : Set ℝ) : MapsTo cos s (Icc (-1 : ℝ) 1) := fun x _ => cos_mem_Icc x
#align real.maps_to_cos Real.mapsTo_cos

/- warning: real.bij_on_sin -> Real.bijOn_sin is a dubious translation:
lean 3 declaration is
  Set.BijOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.BijOn.{0, 0} Real Real Real.sin (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.bij_on_sin Real.bijOn_sinₓ'. -/
theorem bijOn_sin : BijOn sin (Icc (-(π / 2)) (π / 2)) (Icc (-1) 1) :=
  ⟨mapsTo_sin _, injOn_sin, surjOn_sin⟩
#align real.bij_on_sin Real.bijOn_sin

/- warning: real.bij_on_cos -> Real.bijOn_cos is a dubious translation:
lean 3 declaration is
  Set.BijOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) Real.pi) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Set.BijOn.{0, 0} Real Real Real.cos (Set.Icc.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) Real.pi) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.bij_on_cos Real.bijOn_cosₓ'. -/
theorem bijOn_cos : BijOn cos (Icc 0 π) (Icc (-1) 1) :=
  ⟨mapsTo_cos _, injOn_cos, surjOn_cos⟩
#align real.bij_on_cos Real.bijOn_cos

/- warning: real.range_cos -> Real.range_cos is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.cos) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.cos) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.range_cos Real.range_cosₓ'. -/
@[simp]
theorem range_cos : range cos = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 cos_mem_Icc) surjOn_cos.subset_range
#align real.range_cos Real.range_cos

/- warning: real.range_sin -> Real.range_sin is a dubious translation:
lean 3 declaration is
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.sin) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Eq.{1} (Set.{0} Real) (Set.range.{0, 1} Real Real Real.sin) (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.range_sin Real.range_sinₓ'. -/
@[simp]
theorem range_sin : range sin = (Icc (-1) 1 : Set ℝ) :=
  Subset.antisymm (range_subset_iff.2 sin_mem_Icc) surjOn_sin.subset_range
#align real.range_sin Real.range_sin

#print Real.range_cos_infinite /-
theorem range_cos_infinite : (range Real.cos).Infinite :=
  by
  rw [Real.range_cos]
  exact Icc_infinite (by norm_num)
#align real.range_cos_infinite Real.range_cos_infinite
-/

#print Real.range_sin_infinite /-
theorem range_sin_infinite : (range Real.sin).Infinite :=
  by
  rw [Real.range_sin]
  exact Icc_infinite (by norm_num)
#align real.range_sin_infinite Real.range_sin_infinite
-/

section CosDivSq

variable (x : ℝ)

#print Real.sqrtTwoAddSeries /-
/-- the series `sqrt_two_add_series x n` is `sqrt(2 + sqrt(2 + ... ))` with `n` square roots,
  starting with `x`. We define it here because `cos (pi / 2 ^ (n+1)) = sqrt_two_add_series 0 n / 2`
-/
@[simp, pp_nodot]
noncomputable def sqrtTwoAddSeries (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 => sqrt (2 + sqrt_two_add_series n)
#align real.sqrt_two_add_series Real.sqrtTwoAddSeries
-/

#print Real.sqrtTwoAddSeries_zero /-
theorem sqrtTwoAddSeries_zero : sqrtTwoAddSeries x 0 = x := by simp
#align real.sqrt_two_add_series_zero Real.sqrtTwoAddSeries_zero
-/

/- warning: real.sqrt_two_add_series_one -> Real.sqrtTwoAddSeries_one is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Eq.{1} Real (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_one Real.sqrtTwoAddSeries_oneₓ'. -/
theorem sqrtTwoAddSeries_one : sqrtTwoAddSeries 0 1 = sqrt 2 := by simp
#align real.sqrt_two_add_series_one Real.sqrtTwoAddSeries_one

/- warning: real.sqrt_two_add_series_two -> Real.sqrtTwoAddSeries_two is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  Eq.{1} Real (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Real.sqrt (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_two Real.sqrtTwoAddSeries_twoₓ'. -/
theorem sqrtTwoAddSeries_two : sqrtTwoAddSeries 0 2 = sqrt (2 + sqrt 2) := by simp
#align real.sqrt_two_add_series_two Real.sqrtTwoAddSeries_two

/- warning: real.sqrt_two_add_series_zero_nonneg -> Real.sqrtTwoAddSeries_zero_nonneg is a dubious translation:
lean 3 declaration is
  forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n)
but is expected to have type
  forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n)
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_zero_nonneg Real.sqrtTwoAddSeries_zero_nonnegₓ'. -/
theorem sqrtTwoAddSeries_zero_nonneg : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries 0 n
  | 0 => le_refl 0
  | n + 1 => sqrt_nonneg _
#align real.sqrt_two_add_series_zero_nonneg Real.sqrtTwoAddSeries_zero_nonneg

/- warning: real.sqrt_two_add_series_nonneg -> Real.sqrtTwoAddSeries_nonneg is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.sqrtTwoAddSeries x n))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.sqrtTwoAddSeries x n))
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_nonneg Real.sqrtTwoAddSeries_nonnegₓ'. -/
theorem sqrtTwoAddSeries_nonneg {x : ℝ} (h : 0 ≤ x) : ∀ n : ℕ, 0 ≤ sqrtTwoAddSeries x n
  | 0 => h
  | n + 1 => sqrt_nonneg _
#align real.sqrt_two_add_series_nonneg Real.sqrtTwoAddSeries_nonneg

/- warning: real.sqrt_two_add_series_lt_two -> Real.sqrtTwoAddSeries_lt_two is a dubious translation:
lean 3 declaration is
  forall (n : Nat), LT.lt.{0} Real Real.hasLt (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall (n : Nat), LT.lt.{0} Real Real.instLTReal (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_lt_two Real.sqrtTwoAddSeries_lt_twoₓ'. -/
theorem sqrtTwoAddSeries_lt_two : ∀ n : ℕ, sqrtTwoAddSeries 0 n < 2
  | 0 => by norm_num
  | n + 1 => by
    refine' lt_of_lt_of_le _ (sqrt_sq zero_lt_two.le).le
    rw [sqrt_two_add_series, sqrt_lt_sqrt_iff, ← lt_sub_iff_add_lt']
    · refine' (sqrt_two_add_series_lt_two n).trans_le _
      norm_num
    · exact add_nonneg zero_le_two (sqrt_two_add_series_zero_nonneg n)
#align real.sqrt_two_add_series_lt_two Real.sqrtTwoAddSeries_lt_two

/- warning: real.sqrt_two_add_series_succ -> Real.sqrtTwoAddSeries_succ is a dubious translation:
lean 3 declaration is
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.sqrtTwoAddSeries x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Real.sqrtTwoAddSeries (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) x)) n)
but is expected to have type
  forall (x : Real) (n : Nat), Eq.{1} Real (Real.sqrtTwoAddSeries x (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Real.sqrtTwoAddSeries (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) x)) n)
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_succ Real.sqrtTwoAddSeries_succₓ'. -/
theorem sqrtTwoAddSeries_succ (x : ℝ) :
    ∀ n : ℕ, sqrtTwoAddSeries x (n + 1) = sqrtTwoAddSeries (sqrt (2 + x)) n
  | 0 => rfl
  | n + 1 => by rw [sqrt_two_add_series, sqrt_two_add_series_succ, sqrt_two_add_series]
#align real.sqrt_two_add_series_succ Real.sqrtTwoAddSeries_succ

/- warning: real.sqrt_two_add_series_monotone_left -> Real.sqrtTwoAddSeries_monotone_left is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe x y) -> (forall (n : Nat), LE.le.{0} Real Real.hasLe (Real.sqrtTwoAddSeries x n) (Real.sqrtTwoAddSeries y n))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal x y) -> (forall (n : Nat), LE.le.{0} Real Real.instLEReal (Real.sqrtTwoAddSeries x n) (Real.sqrtTwoAddSeries y n))
Case conversion may be inaccurate. Consider using '#align real.sqrt_two_add_series_monotone_left Real.sqrtTwoAddSeries_monotone_leftₓ'. -/
theorem sqrtTwoAddSeries_monotone_left {x y : ℝ} (h : x ≤ y) :
    ∀ n : ℕ, sqrtTwoAddSeries x n ≤ sqrtTwoAddSeries y n
  | 0 => h
  | n + 1 => by
    rw [sqrt_two_add_series, sqrt_two_add_series]
    exact sqrt_le_sqrt (add_le_add_left (sqrt_two_add_series_monotone_left _) _)
#align real.sqrt_two_add_series_monotone_left Real.sqrtTwoAddSeries_monotone_left

#print Real.cos_pi_over_two_pow /-
@[simp]
theorem cos_pi_over_two_pow : ∀ n : ℕ, cos (π / 2 ^ (n + 1)) = sqrtTwoAddSeries 0 n / 2
  | 0 => by simp
  | n + 1 => by
    have : (2 : ℝ) ≠ 0 := two_ne_zero
    symm; rw [div_eq_iff_mul_eq this]; symm
    rw [sqrt_two_add_series, sqrt_eq_iff_sq_eq, mul_pow, cos_sq, ← mul_div_assoc, Nat.add_succ,
      pow_succ, mul_div_mul_left _ _ this, cos_pi_over_two_pow, add_mul]
    congr ; · norm_num
    rw [mul_comm, sq, mul_assoc, ← mul_div_assoc, mul_div_cancel_left, ← mul_div_assoc,
        mul_div_cancel_left] <;>
      try exact this
    apply add_nonneg; norm_num; apply sqrt_two_add_series_zero_nonneg; norm_num
    apply le_of_lt; apply cos_pos_of_mem_Ioo ⟨_, _⟩
    · trans (0 : ℝ)
      rw [neg_lt_zero]
      apply pi_div_two_pos
      apply div_pos pi_pos
      apply pow_pos
      norm_num
    apply div_lt_div' (le_refl π) _ pi_pos _
    refine' lt_of_le_of_lt (le_of_eq (pow_one _).symm) _
    apply pow_lt_pow; norm_num; apply Nat.succ_lt_succ; apply Nat.succ_pos; all_goals norm_num
#align real.cos_pi_over_two_pow Real.cos_pi_over_two_pow
-/

/- warning: real.sin_sq_pi_over_two_pow -> Real.sin_sq_pi_over_two_pow is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align real.sin_sq_pi_over_two_pow Real.sin_sq_pi_over_two_powₓ'. -/
theorem sin_sq_pi_over_two_pow (n : ℕ) :
    sin (π / 2 ^ (n + 1)) ^ 2 = 1 - (sqrtTwoAddSeries 0 n / 2) ^ 2 := by
  rw [sin_sq, cos_pi_over_two_pow]
#align real.sin_sq_pi_over_two_pow Real.sin_sq_pi_over_two_pow

/- warning: real.sin_sq_pi_over_two_pow_succ -> Real.sin_sq_pi_over_two_pow_succ is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) n) (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))
but is expected to have type
  forall (n : Nat), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.sqrtTwoAddSeries (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) n) (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))))))
Case conversion may be inaccurate. Consider using '#align real.sin_sq_pi_over_two_pow_succ Real.sin_sq_pi_over_two_pow_succₓ'. -/
theorem sin_sq_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) ^ 2 = 1 / 2 - sqrtTwoAddSeries 0 n / 4 :=
  by
  rw [sin_sq_pi_over_two_pow, sqrt_two_add_series, div_pow, sq_sqrt, add_div, ← sub_sub]
  congr ; norm_num; norm_num; apply add_nonneg; norm_num; apply sqrt_two_add_series_zero_nonneg
#align real.sin_sq_pi_over_two_pow_succ Real.sin_sq_pi_over_two_pow_succ

#print Real.sin_pi_over_two_pow_succ /-
@[simp]
theorem sin_pi_over_two_pow_succ (n : ℕ) :
    sin (π / 2 ^ (n + 2)) = sqrt (2 - sqrtTwoAddSeries 0 n) / 2 :=
  by
  symm; rw [div_eq_iff_mul_eq]; symm
  rw [sqrt_eq_iff_sq_eq, mul_pow, sin_sq_pi_over_two_pow_succ, sub_mul]
  · congr
    norm_num
    rw [mul_comm]
    convert mul_div_cancel' _ _
    norm_num
    norm_num
  · rw [sub_nonneg]
    apply le_of_lt
    apply sqrt_two_add_series_lt_two
  apply le_of_lt; apply mul_pos; apply sin_pos_of_pos_of_lt_pi
  · apply div_pos pi_pos
    apply pow_pos
    norm_num
  refine' lt_of_lt_of_le _ (le_of_eq (div_one _)); rw [div_lt_div_left]
  refine' lt_of_le_of_lt (le_of_eq (pow_zero 2).symm) _
  apply pow_lt_pow; norm_num; apply Nat.succ_pos; apply pi_pos
  apply pow_pos; all_goals norm_num
#align real.sin_pi_over_two_pow_succ Real.sin_pi_over_two_pow_succ
-/

#print Real.cos_pi_div_four /-
@[simp]
theorem cos_pi_div_four : cos (π / 4) = sqrt 2 / 2 :=
  by
  trans cos (π / 2 ^ 2)
  congr
  norm_num
  simp
#align real.cos_pi_div_four Real.cos_pi_div_four
-/

#print Real.sin_pi_div_four /-
@[simp]
theorem sin_pi_div_four : sin (π / 4) = sqrt 2 / 2 :=
  by
  trans sin (π / 2 ^ 2)
  congr
  norm_num
  simp
#align real.sin_pi_div_four Real.sin_pi_div_four
-/

#print Real.cos_pi_div_eight /-
@[simp]
theorem cos_pi_div_eight : cos (π / 8) = sqrt (2 + sqrt 2) / 2 :=
  by
  trans cos (π / 2 ^ 3)
  congr
  norm_num
  simp
#align real.cos_pi_div_eight Real.cos_pi_div_eight
-/

#print Real.sin_pi_div_eight /-
@[simp]
theorem sin_pi_div_eight : sin (π / 8) = sqrt (2 - sqrt 2) / 2 :=
  by
  trans sin (π / 2 ^ 3)
  congr
  norm_num
  simp
#align real.sin_pi_div_eight Real.sin_pi_div_eight
-/

#print Real.cos_pi_div_sixteen /-
@[simp]
theorem cos_pi_div_sixteen : cos (π / 16) = sqrt (2 + sqrt (2 + sqrt 2)) / 2 :=
  by
  trans cos (π / 2 ^ 4)
  congr
  norm_num
  simp
#align real.cos_pi_div_sixteen Real.cos_pi_div_sixteen
-/

#print Real.sin_pi_div_sixteen /-
@[simp]
theorem sin_pi_div_sixteen : sin (π / 16) = sqrt (2 - sqrt (2 + sqrt 2)) / 2 :=
  by
  trans sin (π / 2 ^ 4)
  congr
  norm_num
  simp
#align real.sin_pi_div_sixteen Real.sin_pi_div_sixteen
-/

#print Real.cos_pi_div_thirty_two /-
@[simp]
theorem cos_pi_div_thirty_two : cos (π / 32) = sqrt (2 + sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
  by
  trans cos (π / 2 ^ 5)
  congr
  norm_num
  simp
#align real.cos_pi_div_thirty_two Real.cos_pi_div_thirty_two
-/

#print Real.sin_pi_div_thirty_two /-
@[simp]
theorem sin_pi_div_thirty_two : sin (π / 32) = sqrt (2 - sqrt (2 + sqrt (2 + sqrt 2))) / 2 :=
  by
  trans sin (π / 2 ^ 5)
  congr
  norm_num
  simp
#align real.sin_pi_div_thirty_two Real.sin_pi_div_thirty_two
-/

#print Real.cos_pi_div_three /-
-- This section is also a convenient location for other explicit values of `sin` and `cos`.
/-- The cosine of `π / 3` is `1 / 2`. -/
@[simp]
theorem cos_pi_div_three : cos (π / 3) = 1 / 2 :=
  by
  have h₁ : (2 * cos (π / 3) - 1) ^ 2 * (2 * cos (π / 3) + 2) = 0 :=
    by
    have : cos (3 * (π / 3)) = cos π := by
      congr 1
      ring
    linarith [cos_pi, cos_three_mul (π / 3)]
  cases' mul_eq_zero.mp h₁ with h h
  · linarith [pow_eq_zero h]
  · have : cos π < cos (π / 3) := by
      refine' cos_lt_cos_of_nonneg_of_le_pi _ rfl.ge _ <;> linarith [pi_pos]
    linarith [cos_pi]
#align real.cos_pi_div_three Real.cos_pi_div_three
-/

/- warning: real.sq_cos_pi_div_six -> Real.sq_cos_pi_div_six is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 6 (OfNat.mk.{0} Real 6 (bit0.{0} Real Real.hasAdd (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.cos (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 6 (instOfNat.{0} Real 6 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 4 (instOfNatNat 4))))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align real.sq_cos_pi_div_six Real.sq_cos_pi_div_sixₓ'. -/
/-- The square of the cosine of `π / 6` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_cos_pi_div_six : cos (π / 6) ^ 2 = 3 / 4 :=
  by
  have h1 : cos (π / 6) ^ 2 = 1 / 2 + 1 / 2 / 2 :=
    by
    convert cos_sq (π / 6)
    have h2 : 2 * (π / 6) = π / 3 := by cancel_denoms
    rw [h2, cos_pi_div_three]
  rw [← sub_eq_zero] at h1⊢
  convert h1 using 1
  ring
#align real.sq_cos_pi_div_six Real.sq_cos_pi_div_six

#print Real.cos_pi_div_six /-
/-- The cosine of `π / 6` is `√3 / 2`. -/
@[simp]
theorem cos_pi_div_six : cos (π / 6) = sqrt 3 / 2 :=
  by
  suffices sqrt 3 = cos (π / 6) * 2
    by
    field_simp [(by norm_num : 0 ≠ 2)]
    exact this.symm
  rw [sqrt_eq_iff_sq_eq]
  · have h1 := (mul_right_inj' (by norm_num : (4 : ℝ) ≠ 0)).mpr sq_cos_pi_div_six
    rw [← sub_eq_zero] at h1⊢
    convert h1 using 1
    ring
  · norm_num
  · have : 0 < cos (π / 6) := by apply cos_pos_of_mem_Ioo <;> constructor <;> linarith [pi_pos]
    linarith
#align real.cos_pi_div_six Real.cos_pi_div_six
-/

#print Real.sin_pi_div_six /-
/-- The sine of `π / 6` is `1 / 2`. -/
@[simp]
theorem sin_pi_div_six : sin (π / 6) = 1 / 2 :=
  by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_three]
  congr
  ring
#align real.sin_pi_div_six Real.sin_pi_div_six
-/

/- warning: real.sq_sin_pi_div_three -> Real.sq_sin_pi_div_three is a dubious translation:
lean 3 declaration is
  Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 3 (OfNat.mk.{0} Real 3 (bit1.{0} Real Real.hasOne Real.hasAdd (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 4 (OfNat.mk.{0} Real 4 (bit0.{0} Real Real.hasAdd (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Real.sin (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 3 (instOfNat.{0} Real 3 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (OfNat.ofNat.{0} Real 4 (instOfNat.{0} Real 4 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))))
Case conversion may be inaccurate. Consider using '#align real.sq_sin_pi_div_three Real.sq_sin_pi_div_threeₓ'. -/
/-- The square of the sine of `π / 3` is `3 / 4` (this is sometimes more convenient than the
result for cosine itself). -/
theorem sq_sin_pi_div_three : sin (π / 3) ^ 2 = 3 / 4 :=
  by
  rw [← cos_pi_div_two_sub, ← sq_cos_pi_div_six]
  congr
  ring
#align real.sq_sin_pi_div_three Real.sq_sin_pi_div_three

#print Real.sin_pi_div_three /-
/-- The sine of `π / 3` is `√3 / 2`. -/
@[simp]
theorem sin_pi_div_three : sin (π / 3) = sqrt 3 / 2 :=
  by
  rw [← cos_pi_div_two_sub, ← cos_pi_div_six]
  congr
  ring
#align real.sin_pi_div_three Real.sin_pi_div_three
-/

end CosDivSq

/- warning: real.sin_order_iso -> Real.sinOrderIso is a dubious translation:
lean 3 declaration is
  OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  OrderIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))))
Case conversion may be inaccurate. Consider using '#align real.sin_order_iso Real.sinOrderIsoₓ'. -/
/-- `real.sin` as an `order_iso` between `[-(π / 2), π / 2]` and `[-1, 1]`. -/
def sinOrderIso : Icc (-(π / 2)) (π / 2) ≃o Icc (-1 : ℝ) 1 :=
  (strictMonoOn_sin.OrderIso _ _).trans <| OrderIso.setCongr _ _ bijOn_sin.image_eq
#align real.sin_order_iso Real.sinOrderIso

/- warning: real.coe_sin_order_iso_apply -> Real.coe_sinOrderIso_apply is a dubious translation:
lean 3 declaration is
  forall (x : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))), Eq.{1} Real ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))))) (coeFn.{1, 1} (OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))) (fun (_x : RelIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) (RelIso.hasCoeToFun.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))) Real.sinOrderIso x)) (Real.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))))) x))
but is expected to have type
  forall (x : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))), Eq.{1} Real (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (fun (_x : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) Real.sinOrderIso x)) (Real.sin (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) x))
Case conversion may be inaccurate. Consider using '#align real.coe_sin_order_iso_apply Real.coe_sinOrderIso_applyₓ'. -/
@[simp]
theorem coe_sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : (sinOrderIso x : ℝ) = sin x :=
  rfl
#align real.coe_sin_order_iso_apply Real.coe_sinOrderIso_apply

/- warning: real.sin_order_iso_apply -> Real.sinOrderIso_apply is a dubious translation:
lean 3 declaration is
  forall (x : coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))), Eq.{1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (coeFn.{1, 1} (OrderIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))))) (fun (_x : RelIso.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))) => (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) -> (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))) (RelIso.hasCoeToFun.{0, 0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))) (LE.le.{0} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Subtype.hasLe.{0} Real Real.hasLe (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))))) Real.sinOrderIso x) (Subtype.mk.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (Real.sin ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))))) x)) (Real.sin_mem_Icc ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (HasLiftT.mk.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (CoeTCₓ.coe.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeBase.{1, 1} (coeSort.{1, 2} (Set.{0} Real) Type (Set.hasCoeToSort.{0} Real) (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) Real (coeSubtype.{1} Real (fun (x : Real) => Membership.Mem.{0, 0} Real (Set.{0} Real) (Set.hasMem.{0} Real) x (Set.Icc.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))))))) x)))
but is expected to have type
  forall (x : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))), Eq.{1} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (FunLike.coe.{1, 1, 1} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (fun (_x : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (RelHomClass.toFunLike.{0, 0, 0} (RelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298)) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298) (RelIso.instRelHomClassRelIso.{0, 0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1281 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (x._@.Mathlib.Order.Hom.Basic._hyg.1283 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) x._@.Mathlib.Order.Hom.Basic._hyg.1281 x._@.Mathlib.Order.Hom.Basic._hyg.1283) (fun (x._@.Mathlib.Order.Hom.Basic._hyg.1296 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (x._@.Mathlib.Order.Hom.Basic._hyg.1298 : Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) => LE.le.{0} (Set.Elem.{0} Real (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Subtype.le.{0} Real Real.instLEReal (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))) x._@.Mathlib.Order.Hom.Basic._hyg.1296 x._@.Mathlib.Order.Hom.Basic._hyg.1298))) Real.sinOrderIso x) (Subtype.mk.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (Real.sin (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) x)) (Real.sin_mem_Icc (Subtype.val.{1} Real (fun (x : Real) => Membership.mem.{0, 0} Real (Set.{0} Real) (Set.instMembershipSet.{0} Real) x (Set.Icc.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) x)))
Case conversion may be inaccurate. Consider using '#align real.sin_order_iso_apply Real.sinOrderIso_applyₓ'. -/
theorem sinOrderIso_apply (x : Icc (-(π / 2)) (π / 2)) : sinOrderIso x = ⟨sin x, sin_mem_Icc x⟩ :=
  rfl
#align real.sin_order_iso_apply Real.sinOrderIso_apply

#print Real.tan_pi_div_four /-
@[simp]
theorem tan_pi_div_four : tan (π / 4) = 1 :=
  by
  rw [tan_eq_sin_div_cos, cos_pi_div_four, sin_pi_div_four]
  have h : sqrt 2 / 2 > 0 := by cancel_denoms
  exact div_self (ne_of_gt h)
#align real.tan_pi_div_four Real.tan_pi_div_four
-/

#print Real.tan_pi_div_two /-
@[simp]
theorem tan_pi_div_two : tan (π / 2) = 0 := by simp [tan_eq_sin_div_cos]
#align real.tan_pi_div_two Real.tan_pi_div_two
-/

/- warning: real.tan_pos_of_pos_of_lt_pi_div_two -> Real.tan_pos_of_pos_of_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.tan x))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.tan x))
Case conversion may be inaccurate. Consider using '#align real.tan_pos_of_pos_of_lt_pi_div_two Real.tan_pos_of_pos_of_lt_pi_div_twoₓ'. -/
theorem tan_pos_of_pos_of_lt_pi_div_two {x : ℝ} (h0x : 0 < x) (hxp : x < π / 2) : 0 < tan x := by
  rw [tan_eq_sin_div_cos] <;>
    exact
      div_pos (sin_pos_of_pos_of_lt_pi h0x (by linarith)) (cos_pos_of_mem_Ioo ⟨by linarith, hxp⟩)
#align real.tan_pos_of_pos_of_lt_pi_div_two Real.tan_pos_of_pos_of_lt_pi_div_two

/- warning: real.tan_nonneg_of_nonneg_of_le_pi_div_two -> Real.tan_nonneg_of_nonneg_of_le_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LE.le.{0} Real Real.hasLe x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Real.tan x))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LE.le.{0} Real Real.instLEReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Real.tan x))
Case conversion may be inaccurate. Consider using '#align real.tan_nonneg_of_nonneg_of_le_pi_div_two Real.tan_nonneg_of_nonneg_of_le_pi_div_twoₓ'. -/
theorem tan_nonneg_of_nonneg_of_le_pi_div_two {x : ℝ} (h0x : 0 ≤ x) (hxp : x ≤ π / 2) : 0 ≤ tan x :=
  match lt_or_eq_of_le h0x, lt_or_eq_of_le hxp with
  | Or.inl hx0, Or.inl hxp => le_of_lt (tan_pos_of_pos_of_lt_pi_div_two hx0 hxp)
  | Or.inl hx0, Or.inr hxp => by simp [hxp, tan_eq_sin_div_cos]
  | Or.inr hx0, _ => by simp [hx0.symm]
#align real.tan_nonneg_of_nonneg_of_le_pi_div_two Real.tan_nonneg_of_nonneg_of_le_pi_div_two

/- warning: real.tan_neg_of_neg_of_pi_div_two_lt -> Real.tan_neg_of_neg_of_pi_div_two_lt is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LT.lt.{0} Real Real.hasLt x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LT.lt.{0} Real Real.hasLt (Real.tan x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LT.lt.{0} Real Real.instLTReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LT.lt.{0} Real Real.instLTReal (Real.tan x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tan_neg_of_neg_of_pi_div_two_lt Real.tan_neg_of_neg_of_pi_div_two_ltₓ'. -/
theorem tan_neg_of_neg_of_pi_div_two_lt {x : ℝ} (hx0 : x < 0) (hpx : -(π / 2) < x) : tan x < 0 :=
  neg_pos.1 (tan_neg x ▸ tan_pos_of_pos_of_lt_pi_div_two (by linarith) (by linarith [pi_pos]))
#align real.tan_neg_of_neg_of_pi_div_two_lt Real.tan_neg_of_neg_of_pi_div_two_lt

/- warning: real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le -> Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le is a dubious translation:
lean 3 declaration is
  forall {x : Real}, (LE.le.{0} Real Real.hasLe x (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (LE.le.{0} Real Real.hasLe (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LE.le.{0} Real Real.hasLe (Real.tan x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {x : Real}, (LE.le.{0} Real Real.instLEReal x (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (LE.le.{0} Real Real.instLEReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LE.le.{0} Real Real.instLEReal (Real.tan x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_leₓ'. -/
theorem tan_nonpos_of_nonpos_of_neg_pi_div_two_le {x : ℝ} (hx0 : x ≤ 0) (hpx : -(π / 2) ≤ x) :
    tan x ≤ 0 :=
  neg_nonneg.1 (tan_neg x ▸ tan_nonneg_of_nonneg_of_le_pi_div_two (by linarith) (by linarith))
#align real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le Real.tan_nonpos_of_nonpos_of_neg_pi_div_two_le

/- warning: real.tan_lt_tan_of_nonneg_of_lt_pi_div_two -> Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) x) -> (LT.lt.{0} Real Real.hasLt y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.tan x) (Real.tan y))
but is expected to have type
  forall {x : Real} {y : Real}, (LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) x) -> (LT.lt.{0} Real Real.instLTReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.tan x) (Real.tan y))
Case conversion may be inaccurate. Consider using '#align real.tan_lt_tan_of_nonneg_of_lt_pi_div_two Real.tan_lt_tan_of_nonneg_of_lt_pi_div_twoₓ'. -/
theorem tan_lt_tan_of_nonneg_of_lt_pi_div_two {x y : ℝ} (hx₁ : 0 ≤ x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos]
  exact
    div_lt_div (sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (le_of_lt hy₂) hxy)
      (cos_le_cos_of_nonneg_of_le_pi hx₁ (by linarith) (le_of_lt hxy))
      (sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith))
      (cos_pos_of_mem_Ioo ⟨by linarith, hy₂⟩)
#align real.tan_lt_tan_of_nonneg_of_lt_pi_div_two Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two

/- warning: real.tan_lt_tan_of_lt_of_lt_pi_div_two -> Real.tan_lt_tan_of_lt_of_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LT.lt.{0} Real Real.hasLt y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt x y) -> (LT.lt.{0} Real Real.hasLt (Real.tan x) (Real.tan y))
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LT.lt.{0} Real Real.instLTReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal x y) -> (LT.lt.{0} Real Real.instLTReal (Real.tan x) (Real.tan y))
Case conversion may be inaccurate. Consider using '#align real.tan_lt_tan_of_lt_of_lt_pi_div_two Real.tan_lt_tan_of_lt_of_lt_pi_div_twoₓ'. -/
theorem tan_lt_tan_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hy₂ : y < π / 2)
    (hxy : x < y) : tan x < tan y :=
  match le_total x 0, le_total y 0 with
  | Or.inl hx0, Or.inl hy0 =>
    neg_lt_neg_iff.1 <| by
      rw [← tan_neg, ← tan_neg] <;>
        exact
          tan_lt_tan_of_nonneg_of_lt_pi_div_two (neg_nonneg.2 hy0) (neg_lt.2 hx₁) (neg_lt_neg hxy)
  | Or.inl hx0, Or.inr hy0 =>
    (lt_or_eq_of_le hy0).elim
      (fun hy0 =>
        calc
          tan x ≤ 0 := tan_nonpos_of_nonpos_of_neg_pi_div_two_le hx0 (le_of_lt hx₁)
          _ < tan y := tan_pos_of_pos_of_lt_pi_div_two hy0 hy₂
          )
      fun hy0 => by
      rw [← hy0, tan_zero] <;> exact tan_neg_of_neg_of_pi_div_two_lt (hy0.symm ▸ hxy) hx₁
  | Or.inr hx0, Or.inl hy0 => by linarith
  | Or.inr hx0, Or.inr hy0 => tan_lt_tan_of_nonneg_of_lt_pi_div_two hx0 hy₂ hxy
#align real.tan_lt_tan_of_lt_of_lt_pi_div_two Real.tan_lt_tan_of_lt_of_lt_pi_div_two

/- warning: real.strict_mono_on_tan -> Real.strictMonoOn_tan is a dubious translation:
lean 3 declaration is
  StrictMonoOn.{0, 0} Real Real Real.preorder Real.preorder Real.tan (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  StrictMonoOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal Real.tan (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.strict_mono_on_tan Real.strictMonoOn_tanₓ'. -/
theorem strictMonoOn_tan : StrictMonoOn tan (Ioo (-(π / 2)) (π / 2)) := fun x hx y hy =>
  tan_lt_tan_of_lt_of_lt_pi_div_two hx.1 hy.2
#align real.strict_mono_on_tan Real.strictMonoOn_tan

/- warning: real.inj_on_tan -> Real.injOn_tan is a dubious translation:
lean 3 declaration is
  Set.InjOn.{0, 0} Real Real Real.tan (Set.Ioo.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))
but is expected to have type
  Set.InjOn.{0, 0} Real Real Real.tan (Set.Ioo.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))
Case conversion may be inaccurate. Consider using '#align real.inj_on_tan Real.injOn_tanₓ'. -/
theorem injOn_tan : InjOn tan (Ioo (-(π / 2)) (π / 2)) :=
  strictMonoOn_tan.InjOn
#align real.inj_on_tan Real.injOn_tan

/- warning: real.tan_inj_of_lt_of_lt_pi_div_two -> Real.tan_inj_of_lt_of_lt_pi_div_two is a dubious translation:
lean 3 declaration is
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) x) -> (LT.lt.{0} Real Real.hasLt x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LT.lt.{0} Real Real.hasLt (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) y) -> (LT.lt.{0} Real Real.hasLt y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (Eq.{1} Real (Real.tan x) (Real.tan y)) -> (Eq.{1} Real x y)
but is expected to have type
  forall {x : Real} {y : Real}, (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) x) -> (LT.lt.{0} Real Real.instLTReal x (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LT.lt.{0} Real Real.instLTReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) y) -> (LT.lt.{0} Real Real.instLTReal y (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (Eq.{1} Real (Real.tan x) (Real.tan y)) -> (Eq.{1} Real x y)
Case conversion may be inaccurate. Consider using '#align real.tan_inj_of_lt_of_lt_pi_div_two Real.tan_inj_of_lt_of_lt_pi_div_twoₓ'. -/
theorem tan_inj_of_lt_of_lt_pi_div_two {x y : ℝ} (hx₁ : -(π / 2) < x) (hx₂ : x < π / 2)
    (hy₁ : -(π / 2) < y) (hy₂ : y < π / 2) (hxy : tan x = tan y) : x = y :=
  injOn_tan ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩ hxy
#align real.tan_inj_of_lt_of_lt_pi_div_two Real.tan_inj_of_lt_of_lt_pi_div_two

#print Real.tan_periodic /-
theorem tan_periodic : Function.Periodic tan π := by
  simpa only [Function.Periodic, tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic
#align real.tan_periodic Real.tan_periodic
-/

#print Real.tan_add_pi /-
theorem tan_add_pi (x : ℝ) : tan (x + π) = tan x :=
  tan_periodic x
#align real.tan_add_pi Real.tan_add_pi
-/

#print Real.tan_sub_pi /-
theorem tan_sub_pi (x : ℝ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x
#align real.tan_sub_pi Real.tan_sub_pi
-/

#print Real.tan_pi_sub /-
theorem tan_pi_sub (x : ℝ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'
#align real.tan_pi_sub Real.tan_pi_sub
-/

#print Real.tan_pi_div_two_sub /-
theorem tan_pi_div_two_sub (x : ℝ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]
#align real.tan_pi_div_two_sub Real.tan_pi_div_two_sub
-/

#print Real.tan_nat_mul_pi /-
theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n
#align real.tan_nat_mul_pi Real.tan_nat_mul_pi
-/

#print Real.tan_int_mul_pi /-
theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n
#align real.tan_int_mul_pi Real.tan_int_mul_pi
-/

#print Real.tan_add_nat_mul_pi /-
theorem tan_add_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x
#align real.tan_add_nat_mul_pi Real.tan_add_nat_mul_pi
-/

#print Real.tan_add_int_mul_pi /-
theorem tan_add_int_mul_pi (x : ℝ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x
#align real.tan_add_int_mul_pi Real.tan_add_int_mul_pi
-/

#print Real.tan_sub_nat_mul_pi /-
theorem tan_sub_nat_mul_pi (x : ℝ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n
#align real.tan_sub_nat_mul_pi Real.tan_sub_nat_mul_pi
-/

#print Real.tan_sub_int_mul_pi /-
theorem tan_sub_int_mul_pi (x : ℝ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n
#align real.tan_sub_int_mul_pi Real.tan_sub_int_mul_pi
-/

#print Real.tan_nat_mul_pi_sub /-
theorem tan_nat_mul_pi_sub (x : ℝ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n
#align real.tan_nat_mul_pi_sub Real.tan_nat_mul_pi_sub
-/

#print Real.tan_int_mul_pi_sub /-
theorem tan_int_mul_pi_sub (x : ℝ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n
#align real.tan_int_mul_pi_sub Real.tan_int_mul_pi_sub
-/

/- warning: real.tendsto_sin_pi_div_two -> Real.tendsto_sin_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.sin (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Set.Iio.{0} Real Real.preorder (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.sin (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Set.Iio.{0} Real Real.instPreorderReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real.tendsto_sin_pi_div_two Real.tendsto_sin_pi_div_twoₓ'. -/
theorem tendsto_sin_pi_div_two : Tendsto sin (𝓝[<] (π / 2)) (𝓝 1) :=
  by
  convert continuous_sin.continuous_within_at
  simp
#align real.tendsto_sin_pi_div_two Real.tendsto_sin_pi_div_two

/- warning: real.tendsto_cos_pi_div_two -> Real.tendsto_cos_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.cos (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Set.Iio.{0} Real Real.preorder (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.cos (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Set.Iio.{0} Real Real.instPreorderReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_cos_pi_div_two Real.tendsto_cos_pi_div_twoₓ'. -/
theorem tendsto_cos_pi_div_two : Tendsto cos (𝓝[<] (π / 2)) (𝓝[>] 0) :=
  by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuous_within_at
    simp
  ·
    filter_upwards [Ioo_mem_nhdsWithin_Iio
        (right_mem_Ioc.mpr (neg_lt_self pi_div_two_pos))]with x hx using cos_pos_of_mem_Ioo hx
#align real.tendsto_cos_pi_div_two Real.tendsto_cos_pi_div_two

/- warning: real.tendsto_tan_pi_div_two -> Real.tendsto_tan_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.tan (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) (Set.Iio.{0} Real Real.preorder (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))))) (Filter.atTop.{0} Real Real.preorder)
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.tan (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) (Set.Iio.{0} Real Real.instPreorderReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))))) (Filter.atTop.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.tendsto_tan_pi_div_two Real.tendsto_tan_pi_div_twoₓ'. -/
theorem tendsto_tan_pi_div_two : Tendsto tan (𝓝[<] (π / 2)) atTop :=
  by
  convert tendsto_cos_pi_div_two.inv_tendsto_zero.at_top_mul zero_lt_one tendsto_sin_pi_div_two
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
#align real.tendsto_tan_pi_div_two Real.tendsto_tan_pi_div_two

/- warning: real.tendsto_sin_neg_pi_div_two -> Real.tendsto_sin_neg_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.sin (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Ioi.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.sin (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Ioi.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) (nhds.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_sin_neg_pi_div_two Real.tendsto_sin_neg_pi_div_twoₓ'. -/
theorem tendsto_sin_neg_pi_div_two : Tendsto sin (𝓝[>] (-(π / 2))) (𝓝 (-1)) :=
  by
  convert continuous_sin.continuous_within_at
  simp
#align real.tendsto_sin_neg_pi_div_two Real.tendsto_sin_neg_pi_div_two

/- warning: real.tendsto_cos_neg_pi_div_two -> Real.tendsto_cos_neg_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.cos (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Ioi.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Set.Ioi.{0} Real Real.preorder (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))))
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.cos (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Ioi.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Set.Ioi.{0} Real Real.instPreorderReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))))
Case conversion may be inaccurate. Consider using '#align real.tendsto_cos_neg_pi_div_two Real.tendsto_cos_neg_pi_div_twoₓ'. -/
theorem tendsto_cos_neg_pi_div_two : Tendsto cos (𝓝[>] (-(π / 2))) (𝓝[>] 0) :=
  by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · convert continuous_cos.continuous_within_at
    simp
  ·
    filter_upwards [Ioo_mem_nhdsWithin_Ioi
        (left_mem_Ico.mpr (neg_lt_self pi_div_two_pos))]with x hx using cos_pos_of_mem_Ioo hx
#align real.tendsto_cos_neg_pi_div_two Real.tendsto_cos_neg_pi_div_two

/- warning: real.tendsto_tan_neg_pi_div_two -> Real.tendsto_tan_neg_pi_div_two is a dubious translation:
lean 3 declaration is
  Filter.Tendsto.{0, 0} Real Real Real.tan (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) (Set.Ioi.{0} Real Real.preorder (Neg.neg.{0} Real Real.hasNeg (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))))) (Filter.atBot.{0} Real Real.preorder)
but is expected to have type
  Filter.Tendsto.{0, 0} Real Real Real.tan (nhdsWithin.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) (Set.Ioi.{0} Real Real.instPreorderReal (Neg.neg.{0} Real Real.instNegReal (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))))) (Filter.atBot.{0} Real Real.instPreorderReal)
Case conversion may be inaccurate. Consider using '#align real.tendsto_tan_neg_pi_div_two Real.tendsto_tan_neg_pi_div_twoₓ'. -/
theorem tendsto_tan_neg_pi_div_two : Tendsto tan (𝓝[>] (-(π / 2))) atBot :=
  by
  convert tendsto_cos_neg_pi_div_two.inv_tendsto_zero.at_top_mul_neg (by norm_num)
      tendsto_sin_neg_pi_div_two
  simp only [Pi.inv_apply, ← div_eq_inv_mul, ← tan_eq_sin_div_cos]
#align real.tendsto_tan_neg_pi_div_two Real.tendsto_tan_neg_pi_div_two

end Real

namespace Complex

open Real

/- warning: complex.sin_eq_zero_iff_cos_eq -> Complex.sin_eq_zero_iff_cos_eq is a dubious translation:
lean 3 declaration is
  forall {z : Complex}, Iff (Eq.{1} Complex (Complex.sin z) (OfNat.ofNat.{0} Complex 0 (OfNat.mk.{0} Complex 0 (Zero.zero.{0} Complex Complex.hasZero)))) (Or (Eq.{1} Complex (Complex.cos z) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))) (Eq.{1} Complex (Complex.cos z) (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))))
but is expected to have type
  forall {z : Complex}, Iff (Eq.{1} Complex (Complex.sin z) (OfNat.ofNat.{0} Complex 0 (Zero.toOfNat0.{0} Complex Complex.instZeroComplex))) (Or (Eq.{1} Complex (Complex.cos z) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))) (Eq.{1} Complex (Complex.cos z) (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))))
Case conversion may be inaccurate. Consider using '#align complex.sin_eq_zero_iff_cos_eq Complex.sin_eq_zero_iff_cos_eqₓ'. -/
theorem sin_eq_zero_iff_cos_eq {z : ℂ} : sin z = 0 ↔ cos z = 1 ∨ cos z = -1 := by
  rw [← mul_self_eq_one_iff, ← sin_sq_add_cos_sq, sq, sq, ← sub_eq_iff_eq_add, sub_self] <;>
    exact ⟨fun h => by rw [h, MulZeroClass.mul_zero], eq_zero_of_mul_self_eq_zero ∘ Eq.symm⟩
#align complex.sin_eq_zero_iff_cos_eq Complex.sin_eq_zero_iff_cos_eq

#print Complex.cos_pi_div_two /-
@[simp]
theorem cos_pi_div_two : cos (π / 2) = 0 :=
  calc
    cos (π / 2) = Real.cos (π / 2) := by rw [of_real_cos] <;> simp
    _ = 0 := by simp
    
#align complex.cos_pi_div_two Complex.cos_pi_div_two
-/

#print Complex.sin_pi_div_two /-
@[simp]
theorem sin_pi_div_two : sin (π / 2) = 1 :=
  calc
    sin (π / 2) = Real.sin (π / 2) := by rw [of_real_sin] <;> simp
    _ = 1 := by simp
    
#align complex.sin_pi_div_two Complex.sin_pi_div_two
-/

#print Complex.sin_pi /-
@[simp]
theorem sin_pi : sin π = 0 := by rw [← of_real_sin, Real.sin_pi] <;> simp
#align complex.sin_pi Complex.sin_pi
-/

#print Complex.cos_pi /-
@[simp]
theorem cos_pi : cos π = -1 := by rw [← of_real_cos, Real.cos_pi] <;> simp
#align complex.cos_pi Complex.cos_pi
-/

#print Complex.sin_two_pi /-
@[simp]
theorem sin_two_pi : sin (2 * π) = 0 := by simp [two_mul, sin_add]
#align complex.sin_two_pi Complex.sin_two_pi
-/

#print Complex.cos_two_pi /-
@[simp]
theorem cos_two_pi : cos (2 * π) = 1 := by simp [two_mul, cos_add]
#align complex.cos_two_pi Complex.cos_two_pi
-/

#print Complex.sin_antiperiodic /-
theorem sin_antiperiodic : Function.Antiperiodic sin π := by simp [sin_add]
#align complex.sin_antiperiodic Complex.sin_antiperiodic
-/

#print Complex.sin_periodic /-
theorem sin_periodic : Function.Periodic sin (2 * π) :=
  sin_antiperiodic.Periodic
#align complex.sin_periodic Complex.sin_periodic
-/

#print Complex.sin_add_pi /-
theorem sin_add_pi (x : ℂ) : sin (x + π) = -sin x :=
  sin_antiperiodic x
#align complex.sin_add_pi Complex.sin_add_pi
-/

#print Complex.sin_add_two_pi /-
theorem sin_add_two_pi (x : ℂ) : sin (x + 2 * π) = sin x :=
  sin_periodic x
#align complex.sin_add_two_pi Complex.sin_add_two_pi
-/

#print Complex.sin_sub_pi /-
theorem sin_sub_pi (x : ℂ) : sin (x - π) = -sin x :=
  sin_antiperiodic.sub_eq x
#align complex.sin_sub_pi Complex.sin_sub_pi
-/

#print Complex.sin_sub_two_pi /-
theorem sin_sub_two_pi (x : ℂ) : sin (x - 2 * π) = sin x :=
  sin_periodic.sub_eq x
#align complex.sin_sub_two_pi Complex.sin_sub_two_pi
-/

#print Complex.sin_pi_sub /-
theorem sin_pi_sub (x : ℂ) : sin (π - x) = sin x :=
  neg_neg (sin x) ▸ sin_neg x ▸ sin_antiperiodic.sub_eq'
#align complex.sin_pi_sub Complex.sin_pi_sub
-/

#print Complex.sin_two_pi_sub /-
theorem sin_two_pi_sub (x : ℂ) : sin (2 * π - x) = -sin x :=
  sin_neg x ▸ sin_periodic.sub_eq'
#align complex.sin_two_pi_sub Complex.sin_two_pi_sub
-/

#print Complex.sin_nat_mul_pi /-
theorem sin_nat_mul_pi (n : ℕ) : sin (n * π) = 0 :=
  sin_antiperiodic.nat_mul_eq_of_eq_zero sin_zero n
#align complex.sin_nat_mul_pi Complex.sin_nat_mul_pi
-/

#print Complex.sin_int_mul_pi /-
theorem sin_int_mul_pi (n : ℤ) : sin (n * π) = 0 :=
  sin_antiperiodic.int_mul_eq_of_eq_zero sin_zero n
#align complex.sin_int_mul_pi Complex.sin_int_mul_pi
-/

#print Complex.sin_add_nat_mul_two_pi /-
theorem sin_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.nat_mul n x
#align complex.sin_add_nat_mul_two_pi Complex.sin_add_nat_mul_two_pi
-/

#print Complex.sin_add_int_mul_two_pi /-
theorem sin_add_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x + n * (2 * π)) = sin x :=
  sin_periodic.int_mul n x
#align complex.sin_add_int_mul_two_pi Complex.sin_add_int_mul_two_pi
-/

#print Complex.sin_sub_nat_mul_two_pi /-
theorem sin_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_nat_mul_eq n
#align complex.sin_sub_nat_mul_two_pi Complex.sin_sub_nat_mul_two_pi
-/

#print Complex.sin_sub_int_mul_two_pi /-
theorem sin_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : sin (x - n * (2 * π)) = sin x :=
  sin_periodic.sub_int_mul_eq n
#align complex.sin_sub_int_mul_two_pi Complex.sin_sub_int_mul_two_pi
-/

#print Complex.sin_nat_mul_two_pi_sub /-
theorem sin_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.nat_mul_sub_eq n
#align complex.sin_nat_mul_two_pi_sub Complex.sin_nat_mul_two_pi_sub
-/

#print Complex.sin_int_mul_two_pi_sub /-
theorem sin_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : sin (n * (2 * π) - x) = -sin x :=
  sin_neg x ▸ sin_periodic.int_mul_sub_eq n
#align complex.sin_int_mul_two_pi_sub Complex.sin_int_mul_two_pi_sub
-/

#print Complex.cos_antiperiodic /-
theorem cos_antiperiodic : Function.Antiperiodic cos π := by simp [cos_add]
#align complex.cos_antiperiodic Complex.cos_antiperiodic
-/

#print Complex.cos_periodic /-
theorem cos_periodic : Function.Periodic cos (2 * π) :=
  cos_antiperiodic.Periodic
#align complex.cos_periodic Complex.cos_periodic
-/

#print Complex.cos_add_pi /-
theorem cos_add_pi (x : ℂ) : cos (x + π) = -cos x :=
  cos_antiperiodic x
#align complex.cos_add_pi Complex.cos_add_pi
-/

#print Complex.cos_add_two_pi /-
theorem cos_add_two_pi (x : ℂ) : cos (x + 2 * π) = cos x :=
  cos_periodic x
#align complex.cos_add_two_pi Complex.cos_add_two_pi
-/

#print Complex.cos_sub_pi /-
theorem cos_sub_pi (x : ℂ) : cos (x - π) = -cos x :=
  cos_antiperiodic.sub_eq x
#align complex.cos_sub_pi Complex.cos_sub_pi
-/

#print Complex.cos_sub_two_pi /-
theorem cos_sub_two_pi (x : ℂ) : cos (x - 2 * π) = cos x :=
  cos_periodic.sub_eq x
#align complex.cos_sub_two_pi Complex.cos_sub_two_pi
-/

#print Complex.cos_pi_sub /-
theorem cos_pi_sub (x : ℂ) : cos (π - x) = -cos x :=
  cos_neg x ▸ cos_antiperiodic.sub_eq'
#align complex.cos_pi_sub Complex.cos_pi_sub
-/

#print Complex.cos_two_pi_sub /-
theorem cos_two_pi_sub (x : ℂ) : cos (2 * π - x) = cos x :=
  cos_neg x ▸ cos_periodic.sub_eq'
#align complex.cos_two_pi_sub Complex.cos_two_pi_sub
-/

#print Complex.cos_nat_mul_two_pi /-
theorem cos_nat_mul_two_pi (n : ℕ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.nat_mul_eq n).trans cos_zero
#align complex.cos_nat_mul_two_pi Complex.cos_nat_mul_two_pi
-/

#print Complex.cos_int_mul_two_pi /-
theorem cos_int_mul_two_pi (n : ℤ) : cos (n * (2 * π)) = 1 :=
  (cos_periodic.int_mul_eq n).trans cos_zero
#align complex.cos_int_mul_two_pi Complex.cos_int_mul_two_pi
-/

#print Complex.cos_add_nat_mul_two_pi /-
theorem cos_add_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.nat_mul n x
#align complex.cos_add_nat_mul_two_pi Complex.cos_add_nat_mul_two_pi
-/

#print Complex.cos_add_int_mul_two_pi /-
theorem cos_add_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x + n * (2 * π)) = cos x :=
  cos_periodic.int_mul n x
#align complex.cos_add_int_mul_two_pi Complex.cos_add_int_mul_two_pi
-/

#print Complex.cos_sub_nat_mul_two_pi /-
theorem cos_sub_nat_mul_two_pi (x : ℂ) (n : ℕ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_nat_mul_eq n
#align complex.cos_sub_nat_mul_two_pi Complex.cos_sub_nat_mul_two_pi
-/

#print Complex.cos_sub_int_mul_two_pi /-
theorem cos_sub_int_mul_two_pi (x : ℂ) (n : ℤ) : cos (x - n * (2 * π)) = cos x :=
  cos_periodic.sub_int_mul_eq n
#align complex.cos_sub_int_mul_two_pi Complex.cos_sub_int_mul_two_pi
-/

#print Complex.cos_nat_mul_two_pi_sub /-
theorem cos_nat_mul_two_pi_sub (x : ℂ) (n : ℕ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.nat_mul_sub_eq n
#align complex.cos_nat_mul_two_pi_sub Complex.cos_nat_mul_two_pi_sub
-/

#print Complex.cos_int_mul_two_pi_sub /-
theorem cos_int_mul_two_pi_sub (x : ℂ) (n : ℤ) : cos (n * (2 * π) - x) = cos x :=
  cos_neg x ▸ cos_periodic.int_mul_sub_eq n
#align complex.cos_int_mul_two_pi_sub Complex.cos_int_mul_two_pi_sub
-/

#print Complex.cos_nat_mul_two_pi_add_pi /-
theorem cos_nat_mul_two_pi_add_pi (n : ℕ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).add_antiperiod_eq cos_antiperiodic
#align complex.cos_nat_mul_two_pi_add_pi Complex.cos_nat_mul_two_pi_add_pi
-/

#print Complex.cos_int_mul_two_pi_add_pi /-
theorem cos_int_mul_two_pi_add_pi (n : ℤ) : cos (n * (2 * π) + π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).add_antiperiod_eq cos_antiperiodic
#align complex.cos_int_mul_two_pi_add_pi Complex.cos_int_mul_two_pi_add_pi
-/

#print Complex.cos_nat_mul_two_pi_sub_pi /-
theorem cos_nat_mul_two_pi_sub_pi (n : ℕ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.nat_mul n).sub_antiperiod_eq cos_antiperiodic
#align complex.cos_nat_mul_two_pi_sub_pi Complex.cos_nat_mul_two_pi_sub_pi
-/

#print Complex.cos_int_mul_two_pi_sub_pi /-
theorem cos_int_mul_two_pi_sub_pi (n : ℤ) : cos (n * (2 * π) - π) = -1 := by
  simpa only [cos_zero] using (cos_periodic.int_mul n).sub_antiperiod_eq cos_antiperiodic
#align complex.cos_int_mul_two_pi_sub_pi Complex.cos_int_mul_two_pi_sub_pi
-/

#print Complex.sin_add_pi_div_two /-
theorem sin_add_pi_div_two (x : ℂ) : sin (x + π / 2) = cos x := by simp [sin_add]
#align complex.sin_add_pi_div_two Complex.sin_add_pi_div_two
-/

#print Complex.sin_sub_pi_div_two /-
theorem sin_sub_pi_div_two (x : ℂ) : sin (x - π / 2) = -cos x := by simp [sub_eq_add_neg, sin_add]
#align complex.sin_sub_pi_div_two Complex.sin_sub_pi_div_two
-/

#print Complex.sin_pi_div_two_sub /-
theorem sin_pi_div_two_sub (x : ℂ) : sin (π / 2 - x) = cos x := by simp [sub_eq_add_neg, sin_add]
#align complex.sin_pi_div_two_sub Complex.sin_pi_div_two_sub
-/

#print Complex.cos_add_pi_div_two /-
theorem cos_add_pi_div_two (x : ℂ) : cos (x + π / 2) = -sin x := by simp [cos_add]
#align complex.cos_add_pi_div_two Complex.cos_add_pi_div_two
-/

#print Complex.cos_sub_pi_div_two /-
theorem cos_sub_pi_div_two (x : ℂ) : cos (x - π / 2) = sin x := by simp [sub_eq_add_neg, cos_add]
#align complex.cos_sub_pi_div_two Complex.cos_sub_pi_div_two
-/

#print Complex.cos_pi_div_two_sub /-
theorem cos_pi_div_two_sub (x : ℂ) : cos (π / 2 - x) = sin x := by
  rw [← cos_neg, neg_sub, cos_sub_pi_div_two]
#align complex.cos_pi_div_two_sub Complex.cos_pi_div_two_sub
-/

#print Complex.tan_periodic /-
theorem tan_periodic : Function.Periodic tan π := by
  simpa only [tan_eq_sin_div_cos] using sin_antiperiodic.div cos_antiperiodic
#align complex.tan_periodic Complex.tan_periodic
-/

#print Complex.tan_add_pi /-
theorem tan_add_pi (x : ℂ) : tan (x + π) = tan x :=
  tan_periodic x
#align complex.tan_add_pi Complex.tan_add_pi
-/

#print Complex.tan_sub_pi /-
theorem tan_sub_pi (x : ℂ) : tan (x - π) = tan x :=
  tan_periodic.sub_eq x
#align complex.tan_sub_pi Complex.tan_sub_pi
-/

#print Complex.tan_pi_sub /-
theorem tan_pi_sub (x : ℂ) : tan (π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.sub_eq'
#align complex.tan_pi_sub Complex.tan_pi_sub
-/

#print Complex.tan_pi_div_two_sub /-
theorem tan_pi_div_two_sub (x : ℂ) : tan (π / 2 - x) = (tan x)⁻¹ := by
  rw [tan_eq_sin_div_cos, tan_eq_sin_div_cos, inv_div, sin_pi_div_two_sub, cos_pi_div_two_sub]
#align complex.tan_pi_div_two_sub Complex.tan_pi_div_two_sub
-/

#print Complex.tan_nat_mul_pi /-
theorem tan_nat_mul_pi (n : ℕ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.nat_mul_eq n
#align complex.tan_nat_mul_pi Complex.tan_nat_mul_pi
-/

#print Complex.tan_int_mul_pi /-
theorem tan_int_mul_pi (n : ℤ) : tan (n * π) = 0 :=
  tan_zero ▸ tan_periodic.int_mul_eq n
#align complex.tan_int_mul_pi Complex.tan_int_mul_pi
-/

#print Complex.tan_add_nat_mul_pi /-
theorem tan_add_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x + n * π) = tan x :=
  tan_periodic.nat_mul n x
#align complex.tan_add_nat_mul_pi Complex.tan_add_nat_mul_pi
-/

#print Complex.tan_add_int_mul_pi /-
theorem tan_add_int_mul_pi (x : ℂ) (n : ℤ) : tan (x + n * π) = tan x :=
  tan_periodic.int_mul n x
#align complex.tan_add_int_mul_pi Complex.tan_add_int_mul_pi
-/

#print Complex.tan_sub_nat_mul_pi /-
theorem tan_sub_nat_mul_pi (x : ℂ) (n : ℕ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_nat_mul_eq n
#align complex.tan_sub_nat_mul_pi Complex.tan_sub_nat_mul_pi
-/

#print Complex.tan_sub_int_mul_pi /-
theorem tan_sub_int_mul_pi (x : ℂ) (n : ℤ) : tan (x - n * π) = tan x :=
  tan_periodic.sub_int_mul_eq n
#align complex.tan_sub_int_mul_pi Complex.tan_sub_int_mul_pi
-/

#print Complex.tan_nat_mul_pi_sub /-
theorem tan_nat_mul_pi_sub (x : ℂ) (n : ℕ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.nat_mul_sub_eq n
#align complex.tan_nat_mul_pi_sub Complex.tan_nat_mul_pi_sub
-/

#print Complex.tan_int_mul_pi_sub /-
theorem tan_int_mul_pi_sub (x : ℂ) (n : ℤ) : tan (n * π - x) = -tan x :=
  tan_neg x ▸ tan_periodic.int_mul_sub_eq n
#align complex.tan_int_mul_pi_sub Complex.tan_int_mul_pi_sub
-/

/- warning: complex.exp_antiperiodic -> Complex.exp_antiperiodic is a dubious translation:
lean 3 declaration is
  Function.Antiperiodic.{0, 0} Complex Complex Complex.hasAdd Complex.hasNeg Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I)
but is expected to have type
  Function.Antiperiodic.{0, 0} Complex Complex Complex.instAddComplex Complex.instNegComplex Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.exp_antiperiodic Complex.exp_antiperiodicₓ'. -/
theorem exp_antiperiodic : Function.Antiperiodic exp (π * I) := by simp [exp_add, exp_mul_I]
#align complex.exp_antiperiodic Complex.exp_antiperiodic

/- warning: complex.exp_periodic -> Complex.exp_periodic is a dubious translation:
lean 3 declaration is
  Function.Periodic.{0, 0} Complex Complex Complex.hasAdd Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I)
but is expected to have type
  Function.Periodic.{0, 0} Complex Complex Complex.instAddComplex Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I)
Case conversion may be inaccurate. Consider using '#align complex.exp_periodic Complex.exp_periodicₓ'. -/
theorem exp_periodic : Function.Periodic exp (2 * π * I) :=
  (mul_assoc (2 : ℂ) π I).symm ▸ exp_antiperiodic.Periodic
#align complex.exp_periodic Complex.exp_periodic

/- warning: complex.exp_mul_I_antiperiodic -> Complex.exp_mul_I_antiperiodic is a dubious translation:
lean 3 declaration is
  Function.Antiperiodic.{0, 0} Complex Complex Complex.hasAdd Complex.hasNeg (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)
but is expected to have type
  Function.Antiperiodic.{0, 0} Complex Complex Complex.instAddComplex Complex.instNegComplex (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I)) (Complex.ofReal' Real.pi)
Case conversion may be inaccurate. Consider using '#align complex.exp_mul_I_antiperiodic Complex.exp_mul_I_antiperiodicₓ'. -/
theorem exp_mul_I_antiperiodic : Function.Antiperiodic (fun x => exp (x * I)) π := by
  simpa only [mul_inv_cancel_right₀ I_ne_zero] using exp_antiperiodic.mul_const I_ne_zero
#align complex.exp_mul_I_antiperiodic Complex.exp_mul_I_antiperiodic

/- warning: complex.exp_mul_I_periodic -> Complex.exp_mul_I_periodic is a dubious translation:
lean 3 declaration is
  Function.Periodic.{0, 0} Complex Complex Complex.hasAdd (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) x Complex.I)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi))
but is expected to have type
  Function.Periodic.{0, 0} Complex Complex Complex.instAddComplex (fun (x : Complex) => Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) x Complex.I)) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi))
Case conversion may be inaccurate. Consider using '#align complex.exp_mul_I_periodic Complex.exp_mul_I_periodicₓ'. -/
theorem exp_mul_I_periodic : Function.Periodic (fun x => exp (x * I)) (2 * π) :=
  exp_mul_I_antiperiodic.Periodic
#align complex.exp_mul_I_periodic Complex.exp_mul_I_periodic

/- warning: complex.exp_pi_mul_I -> Complex.exp_pi_mul_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I)) (Neg.neg.{0} Complex Complex.hasNeg (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne))))
but is expected to have type
  Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I)) (Neg.neg.{0} Complex Complex.instNegComplex (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex)))
Case conversion may be inaccurate. Consider using '#align complex.exp_pi_mul_I Complex.exp_pi_mul_Iₓ'. -/
@[simp]
theorem exp_pi_mul_I : exp (π * I) = -1 :=
  exp_zero ▸ exp_antiperiodic.Eq
#align complex.exp_pi_mul_I Complex.exp_pi_mul_I

/- warning: complex.exp_two_pi_mul_I -> Complex.exp_two_pi_mul_I is a dubious translation:
lean 3 declaration is
  Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I)) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I)) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.exp_two_pi_mul_I Complex.exp_two_pi_mul_Iₓ'. -/
@[simp]
theorem exp_two_pi_mul_I : exp (2 * π * I) = 1 :=
  exp_periodic.Eq.trans exp_zero
#align complex.exp_two_pi_mul_I Complex.exp_two_pi_mul_I

/- warning: complex.exp_nat_mul_two_pi_mul_I -> Complex.exp_nat_mul_two_pi_mul_I is a dubious translation:
lean 3 declaration is
  forall (n : Nat), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Nat Complex (HasLiftT.mk.{1, 1} Nat Complex (CoeTCₓ.coe.{1, 1} Nat Complex (Nat.castCoe.{0} Complex (AddMonoidWithOne.toNatCast.{0} Complex (AddGroupWithOne.toAddMonoidWithOne.{0} Complex Complex.addGroupWithOne))))) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (n : Nat), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Nat.cast.{0} Complex (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.exp_nat_mul_two_pi_mul_I Complex.exp_nat_mul_two_pi_mul_Iₓ'. -/
@[simp]
theorem exp_nat_mul_two_pi_mul_I (n : ℕ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.nat_mul_eq n).trans exp_zero
#align complex.exp_nat_mul_two_pi_mul_I Complex.exp_nat_mul_two_pi_mul_I

/- warning: complex.exp_int_mul_two_pi_mul_I -> Complex.exp_int_mul_two_pi_mul_I is a dubious translation:
lean 3 declaration is
  forall (n : Int), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Int Complex (HasLiftT.mk.{1, 1} Int Complex (CoeTCₓ.coe.{1, 1} Int Complex (Int.castCoe.{0} Complex (AddGroupWithOne.toHasIntCast.{0} Complex Complex.addGroupWithOne)))) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (OfNat.ofNat.{0} Complex 2 (OfNat.mk.{0} Complex 2 (bit0.{0} Complex Complex.hasAdd (One.one.{0} Complex Complex.hasOne)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi)) Complex.I))) (OfNat.ofNat.{0} Complex 1 (OfNat.mk.{0} Complex 1 (One.one.{0} Complex Complex.hasOne)))
but is expected to have type
  forall (n : Int), Eq.{1} Complex (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Int.cast.{0} Complex (Ring.toIntCast.{0} Complex Complex.instRingComplex) n) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (OfNat.ofNat.{0} Complex 2 (instOfNat.{0} Complex 2 (Semiring.toNatCast.{0} Complex Complex.instSemiringComplex) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Complex.ofReal' Real.pi)) Complex.I))) (OfNat.ofNat.{0} Complex 1 (One.toOfNat1.{0} Complex Complex.instOneComplex))
Case conversion may be inaccurate. Consider using '#align complex.exp_int_mul_two_pi_mul_I Complex.exp_int_mul_two_pi_mul_Iₓ'. -/
@[simp]
theorem exp_int_mul_two_pi_mul_I (n : ℤ) : exp (n * (2 * π * I)) = 1 :=
  (exp_periodic.int_mul_eq n).trans exp_zero
#align complex.exp_int_mul_two_pi_mul_I Complex.exp_int_mul_two_pi_mul_I

/- warning: complex.exp_add_pi_mul_I -> Complex.exp_add_pi_mul_I is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) z (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I))) (Neg.neg.{0} Complex Complex.hasNeg (Complex.exp z))
but is expected to have type
  forall (z : Complex), Eq.{1} Complex (Complex.exp (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) z (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I))) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.exp z))
Case conversion may be inaccurate. Consider using '#align complex.exp_add_pi_mul_I Complex.exp_add_pi_mul_Iₓ'. -/
@[simp]
theorem exp_add_pi_mul_I (z : ℂ) : exp (z + π * I) = -exp z :=
  exp_antiperiodic z
#align complex.exp_add_pi_mul_I Complex.exp_add_pi_mul_I

/- warning: complex.exp_sub_pi_mul_I -> Complex.exp_sub_pi_mul_I is a dubious translation:
lean 3 declaration is
  forall (z : Complex), Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.hasSub) z (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) Real.pi) Complex.I))) (Neg.neg.{0} Complex Complex.hasNeg (Complex.exp z))
but is expected to have type
  forall (z : Complex), Eq.{1} Complex (Complex.exp (HSub.hSub.{0, 0, 0} Complex Complex Complex (instHSub.{0} Complex Complex.instSubComplex) z (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' Real.pi) Complex.I))) (Neg.neg.{0} Complex Complex.instNegComplex (Complex.exp z))
Case conversion may be inaccurate. Consider using '#align complex.exp_sub_pi_mul_I Complex.exp_sub_pi_mul_Iₓ'. -/
@[simp]
theorem exp_sub_pi_mul_I (z : ℂ) : exp (z - π * I) = -exp z :=
  exp_antiperiodic.sub_eq z
#align complex.exp_sub_pi_mul_I Complex.exp_sub_pi_mul_I

/- warning: complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le -> Complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le is a dubious translation:
lean 3 declaration is
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.hasLe a (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (forall {z : Complex}, (LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.im z)) b) -> (LE.le.{0} Real Real.hasLe b (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) Real.pi (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))) -> (LE.le.{0} Real Real.hasLe (coeFn.{1, 1} (AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) (fun (f : AbsoluteValue.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) => Complex -> Real) (AbsoluteValue.hasCoeToFun.{0, 0} Complex Real (Ring.toSemiring.{0} Complex Complex.ring) Real.orderedSemiring) Complex.abs (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) Real Complex (HasLiftT.mk.{1, 1} Real Complex (CoeTCₓ.coe.{1, 1} Real Complex (coeBase.{1, 1} Real Complex Complex.hasCoe))) a) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.hasAdd) (Complex.exp z) (Complex.exp (Neg.neg.{0} Complex Complex.hasNeg z)))))) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) a (Real.cos b)) (Real.exp (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Complex.re z)))))))
but is expected to have type
  forall {a : Real} {b : Real}, (LE.le.{0} Real Real.instLEReal a (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (forall {z : Complex}, (LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.im z)) b) -> (LE.le.{0} Real Real.instLEReal b (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) Real.pi (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))) -> (LE.le.{0} ((fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' a) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.exp z) (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex z)))))) Real.instLEReal (FunLike.coe.{1, 1, 1} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex (fun (f : Complex) => (fun (x._@.Mathlib.Algebra.Order.Hom.Basic._hyg.99 : Complex) => Real) f) (SubadditiveHomClass.toFunLike.{0, 0, 0} (AbsoluteValue.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring) Complex Real (Distrib.toAdd.{0} Complex (NonUnitalNonAssocSemiring.toDistrib.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex Complex.instSemiringComplex)))) (Distrib.toAdd.{0} Real (NonUnitalNonAssocSemiring.toDistrib.{0} Real (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Real (Semiring.toNonAssocSemiring.{0} Real (OrderedSemiring.toSemiring.{0} Real Real.orderedSemiring))))) (Preorder.toLE.{0} Real (PartialOrder.toPreorder.{0} Real (OrderedSemiring.toPartialOrder.{0} Real Real.orderedSemiring))) (AbsoluteValue.subadditiveHomClass.{0, 0} Complex Real Complex.instSemiringComplex Real.orderedSemiring)) Complex.abs (Complex.exp (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.instMulComplex) (Complex.ofReal' a) (HAdd.hAdd.{0, 0, 0} Complex Complex Complex (instHAdd.{0} Complex Complex.instAddComplex) (Complex.exp z) (Complex.exp (Neg.neg.{0} Complex Complex.instNegComplex z)))))) (Real.exp (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) a (Real.cos b)) (Real.exp (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Complex.re z)))))))
Case conversion may be inaccurate. Consider using '#align complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le Complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_leₓ'. -/
/-- A supporting lemma for the **Phragmen-Lindelöf principle** in a horizontal strip. If `z : ℂ`
belongs to a horizontal strip `|complex.im z| ≤ b`, `b ≤ π / 2`, and `a ≤ 0`, then
$$\left|exp^{a\left(e^{z}+e^{-z}\right)}\right| \le e^{a\cos b \exp^{|re z|}}.$$
-/
theorem abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le {a b : ℝ} (ha : a ≤ 0) {z : ℂ} (hz : |z.im| ≤ b)
    (hb : b ≤ π / 2) :
    abs (exp (a * (exp z + exp (-z)))) ≤ Real.exp (a * Real.cos b * Real.exp (|z.re|)) :=
  by
  simp only [abs_exp, Real.exp_le_exp, of_real_mul_re, add_re, exp_re, neg_im, Real.cos_neg, ←
    add_mul, mul_assoc, mul_comm (Real.cos b), neg_re, ← Real.cos_abs z.im]
  have : Real.exp (|z.re|) ≤ Real.exp z.re + Real.exp (-z.re) :=
    apply_abs_le_add_of_nonneg (fun x => (Real.exp_pos x).le) z.re
  refine' mul_le_mul_of_nonpos_left (mul_le_mul this _ _ ((Real.exp_pos _).le.trans this)) ha
  ·
    exact
      Real.cos_le_cos_of_nonneg_of_le_pi (_root_.abs_nonneg _)
        (hb.trans <| half_le_self <| real.pi_pos.le) hz
  · refine' Real.cos_nonneg_of_mem_Icc ⟨_, hb⟩
    exact (neg_nonpos.2 <| real.pi_div_two_pos.le).trans ((_root_.abs_nonneg _).trans hz)
#align complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le Complex.abs_exp_mul_exp_add_exp_neg_le_of_abs_im_le

end Complex

