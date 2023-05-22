/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey

! This file was ported from Lean 3 source module analysis.special_functions.log.monotone
! leanprover-community/mathlib commit 1b0a28e1c93409dbf6d69526863cd9984ef652ce
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Pow.Real

/-!
# Logarithm Tonality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we describe the tonality of the logarithm function when multiplied by functions of the
form `x ^ a`.

## Tags

logarithm, tonality
-/


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : ℝ}

/- warning: real.log_mul_self_monotone_on -> Real.log_mul_self_monotoneOn is a dubious translation:
lean 3 declaration is
  MonotoneOn.{0, 0} Real Real Real.preorder Real.preorder (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Real.log x) x) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) x))
but is expected to have type
  MonotoneOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (fun (x : Real) => HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Real.log x) x) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) x))
Case conversion may be inaccurate. Consider using '#align real.log_mul_self_monotone_on Real.log_mul_self_monotoneOnₓ'. -/
theorem log_mul_self_monotoneOn : MonotoneOn (fun x : ℝ => log x * x) { x | 1 ≤ x } :=
  by
  -- TODO: can be strengthened to exp (-1) ≤ x
  simp only [MonotoneOn, mem_set_of_eq]
  intro x hex y hey hxy
  have x_pos : 0 < x := lt_of_lt_of_le zero_lt_one hex
  have y_pos : 0 < y := lt_of_lt_of_le zero_lt_one hey
  refine' mul_le_mul ((log_le_log x_pos y_pos).mpr hxy) hxy (le_of_lt x_pos) _
  rwa [le_log_iff_exp_le y_pos, Real.exp_zero]
#align real.log_mul_self_monotone_on Real.log_mul_self_monotoneOn

/- warning: real.log_div_self_antitone_on -> Real.log_div_self_antitoneOn is a dubious translation:
lean 3 declaration is
  AntitoneOn.{0, 0} Real Real Real.preorder Real.preorder (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) x) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (Real.exp (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) x))
but is expected to have type
  AntitoneOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) x) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.instLEReal (Real.exp (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) x))
Case conversion may be inaccurate. Consider using '#align real.log_div_self_antitone_on Real.log_div_self_antitoneOnₓ'. -/
theorem log_div_self_antitoneOn : AntitoneOn (fun x : ℝ => log x / x) { x | exp 1 ≤ x } :=
  by
  simp only [AntitoneOn, mem_set_of_eq]
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 ≤ log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 ≤ y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff x_pos, zero_add, one_mul]
  rw [div_le_iff y_pos, ← sub_le_sub_iff_right (log x)]
  calc
    log y - log x = log (y / x) := by rw [log_div y_pos.ne' x_pos.ne']
    _ ≤ y / x - 1 := (log_le_sub_one_of_pos (div_pos y_pos x_pos))
    _ ≤ log x * (y / x - 1) := (le_mul_of_one_le_left hyx hlogx)
    _ = log x / x * y - log x := by ring
    
#align real.log_div_self_antitone_on Real.log_div_self_antitoneOn

/- warning: real.log_div_self_rpow_antitone_on -> Real.log_div_self_rpow_antitoneOn is a dubious translation:
lean 3 declaration is
  forall {a : Real}, (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) a) -> (AntitoneOn.{0, 0} Real Real Real.preorder Real.preorder (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.hasPow) x a)) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (Real.exp (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))) a)) x)))
but is expected to have type
  forall {a : Real}, (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) a) -> (AntitoneOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) (HPow.hPow.{0, 0, 0} Real Real Real (instHPow.{0, 0} Real Real Real.instPowReal) x a)) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.instLEReal (Real.exp (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)) a)) x)))
Case conversion may be inaccurate. Consider using '#align real.log_div_self_rpow_antitone_on Real.log_div_self_rpow_antitoneOnₓ'. -/
theorem log_div_self_rpow_antitoneOn {a : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ => log x / x ^ a) { x | exp (1 / a) ≤ x } :=
  by
  simp only [AntitoneOn, mem_set_of_eq]
  intro x hex y hey hxy
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos (1 / a)) hex
  have y_pos : 0 < y := by linarith
  have x_nonneg : 0 ≤ x := le_trans (le_of_lt (exp_pos (1 / a))) hex
  have y_nonneg : 0 ≤ y := by linarith
  nth_rw 1 [← rpow_one y]
  nth_rw 1 [← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm, div_eq_mul_one_div a a, rpow_mul y_nonneg, rpow_mul x_nonneg,
    log_rpow (rpow_pos_of_pos y_pos a), log_rpow (rpow_pos_of_pos x_pos a), mul_div_assoc,
    mul_div_assoc, mul_le_mul_left (one_div_pos.mpr ha)]
  · refine' log_div_self_antitone_on _ _ _
    · simp only [Set.mem_setOf_eq]
      convert rpow_le_rpow _ hex (le_of_lt ha)
      rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field_simp [(ne_of_lt ha).symm]
      exact le_of_lt (exp_pos (1 / a))
    · simp only [Set.mem_setOf_eq]
      convert rpow_le_rpow _ (trans hex hxy) (le_of_lt ha)
      rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field_simp [(ne_of_lt ha).symm]
      exact le_of_lt (exp_pos (1 / a))
    exact rpow_le_rpow x_nonneg hxy (le_of_lt ha)
#align real.log_div_self_rpow_antitone_on Real.log_div_self_rpow_antitoneOn

/- warning: real.log_div_sqrt_antitone_on -> Real.log_div_sqrt_antitoneOn is a dubious translation:
lean 3 declaration is
  AntitoneOn.{0, 0} Real Real Real.preorder Real.preorder (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Real.log x) (Real.sqrt x)) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.hasLe (Real.exp (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne))))) x))
but is expected to have type
  AntitoneOn.{0, 0} Real Real Real.instPreorderReal Real.instPreorderReal (fun (x : Real) => HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Real.log x) (Real.sqrt x)) (setOf.{0} Real (fun (x : Real) => LE.le.{0} Real Real.instLEReal (Real.exp (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))))) x))
Case conversion may be inaccurate. Consider using '#align real.log_div_sqrt_antitone_on Real.log_div_sqrt_antitoneOnₓ'. -/
theorem log_div_sqrt_antitoneOn : AntitoneOn (fun x : ℝ => log x / sqrt x) { x | exp 2 ≤ x } :=
  by
  simp_rw [sqrt_eq_rpow]
  convert@log_div_self_rpow_antitone_on (1 / 2) (by norm_num)
  norm_num
#align real.log_div_sqrt_antitone_on Real.log_div_sqrt_antitoneOn

end Real

