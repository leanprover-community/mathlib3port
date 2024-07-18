/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import Algebra.ContinuedFractions.Basic

#align_import algebra.continued_fractions.translations from "leanprover-community/mathlib"@"b5ad141426bb005414324f89719c77c0aa3ec612"

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`algebra.continued_fractions.basic`.
-/


namespace GenContFract

/- ././././Mathport/Syntax/Translate/Command.lean:230:11: unsupported: unusual advanced open style -/
section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type _} {g : GenContFract α} {n : ℕ}

#print GenContFract.terminatedAt_iff_s_terminatedAt /-
theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_terminated_at GenContFract.terminatedAt_iff_s_terminatedAt
-/

#print GenContFract.terminatedAt_iff_s_none /-
theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_none GenContFract.terminatedAt_iff_s_none
-/

#print GenContFract.partNum_none_iff_s_none /-
theorem partNum_none_iff_s_none : g.partNums.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [partial_numerators, s_nth_eq]
#align generalized_continued_fraction.part_num_none_iff_s_none GenContFract.partNum_none_iff_s_none
-/

#print GenContFract.terminatedAt_iff_partNum_none /-
theorem terminatedAt_iff_partNum_none : g.TerminatedAt n ↔ g.partNums.get? n = none := by
  rw [terminated_at_iff_s_none, part_num_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_num_none GenContFract.terminatedAt_iff_partNum_none
-/

#print GenContFract.partDen_none_iff_s_none /-
theorem partDen_none_iff_s_none : g.partDens.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [partial_denominators, s_nth_eq]
#align generalized_continued_fraction.part_denom_none_iff_s_none GenContFract.partDen_none_iff_s_none
-/

#print GenContFract.terminatedAt_iff_partDen_none /-
theorem terminatedAt_iff_partDen_none : g.TerminatedAt n ↔ g.partDens.get? n = none := by
  rw [terminated_at_iff_s_none, part_denom_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_denom_none GenContFract.terminatedAt_iff_partDen_none
-/

#print GenContFract.partNum_eq_s_a /-
theorem partNum_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partNums.get? n = some gp.a := by simp [partial_numerators, s_nth_eq]
#align generalized_continued_fraction.part_num_eq_s_a GenContFract.partNum_eq_s_a
-/

#print GenContFract.partDen_eq_s_b /-
theorem partDen_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partDens.get? n = some gp.b := by simp [partial_denominators, s_nth_eq]
#align generalized_continued_fraction.part_denom_eq_s_b GenContFract.partDen_eq_s_b
-/

#print GenContFract.exists_s_a_of_partNum /-
theorem exists_s_a_of_partNum {a : α} (nth_part_num_eq : g.partNums.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  simpa [partial_numerators, seq.map_nth] using nth_part_num_eq
#align generalized_continued_fraction.exists_s_a_of_part_num GenContFract.exists_s_a_of_partNum
-/

#print GenContFract.exists_s_b_of_partDen /-
theorem exists_s_b_of_partDen {b : α} (nth_part_denom_eq : g.partDens.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partial_denominators, seq.map_nth] using nth_part_denom_eq
#align generalized_continued_fraction.exists_s_b_of_part_denom GenContFract.exists_s_b_of_partDen
-/

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type _} {g : GenContFract K} {n : ℕ} [DivisionRing K]

#print GenContFract.nth_cont_eq_succ_nth_contAux /-
theorem nth_cont_eq_succ_nth_contAux : g.conts n = g.contsAux (n + 1) :=
  rfl
#align generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux GenContFract.nth_cont_eq_succ_nth_contAux
-/

#print GenContFract.num_eq_conts_a /-
theorem num_eq_conts_a : g.nums n = (g.conts n).a :=
  rfl
#align generalized_continued_fraction.num_eq_conts_a GenContFract.num_eq_conts_a
-/

#print GenContFract.den_eq_conts_b /-
theorem den_eq_conts_b : g.dens n = (g.conts n).b :=
  rfl
#align generalized_continued_fraction.denom_eq_conts_b GenContFract.den_eq_conts_b
-/

#print GenContFract.conv_eq_num_div_den /-
theorem conv_eq_num_div_den : g.convs n = g.nums n / g.dens n :=
  rfl
#align generalized_continued_fraction.convergent_eq_num_div_denom GenContFract.conv_eq_num_div_den
-/

#print GenContFract.conv_eq_conts_a_div_conts_b /-
theorem conv_eq_conts_a_div_conts_b : g.convs n = (g.conts n).a / (g.conts n).b :=
  rfl
#align generalized_continued_fraction.convergent_eq_conts_a_div_conts_b GenContFract.conv_eq_conts_a_div_conts_b
-/

#print GenContFract.exists_conts_a_of_num /-
theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.nums n = A) :
    ∃ conts, g.conts n = conts ∧ conts.a = A := by simpa
#align generalized_continued_fraction.exists_conts_a_of_num GenContFract.exists_conts_a_of_num
-/

#print GenContFract.exists_conts_b_of_den /-
theorem exists_conts_b_of_den {B : K} (nth_denom_eq : g.dens n = B) :
    ∃ conts, g.conts n = conts ∧ conts.b = B := by simpa
#align generalized_continued_fraction.exists_conts_b_of_denom GenContFract.exists_conts_b_of_den
-/

#print GenContFract.zeroth_contAux_eq_one_zero /-
@[simp]
theorem zeroth_contAux_eq_one_zero : g.contsAux 0 = ⟨1, 0⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero GenContFract.zeroth_contAux_eq_one_zero
-/

#print GenContFract.first_contAux_eq_h_one /-
@[simp]
theorem first_contAux_eq_h_one : g.contsAux 1 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.first_continuant_aux_eq_h_one GenContFract.first_contAux_eq_h_one
-/

#print GenContFract.zeroth_cont_eq_h_one /-
@[simp]
theorem zeroth_cont_eq_h_one : g.conts 0 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_eq_h_one GenContFract.zeroth_cont_eq_h_one
-/

#print GenContFract.zeroth_num_eq_h /-
@[simp]
theorem zeroth_num_eq_h : g.nums 0 = g.h :=
  rfl
#align generalized_continued_fraction.zeroth_numerator_eq_h GenContFract.zeroth_num_eq_h
-/

#print GenContFract.zeroth_den_eq_one /-
@[simp]
theorem zeroth_den_eq_one : g.dens 0 = 1 :=
  rfl
#align generalized_continued_fraction.zeroth_denominator_eq_one GenContFract.zeroth_den_eq_one
-/

#print GenContFract.zeroth_conv_eq_h /-
@[simp]
theorem zeroth_conv_eq_h : g.convs 0 = g.h := by
  simp [convergent_eq_num_div_denom, num_eq_conts_a, denom_eq_conts_b, div_one]
#align generalized_continued_fraction.zeroth_convergent_eq_h GenContFract.zeroth_conv_eq_h
-/

#print GenContFract.second_contAux_eq /-
theorem second_contAux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.contsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, continuants_aux, next_continuants, next_denominator, next_numerator]
#align generalized_continued_fraction.second_continuant_aux_eq GenContFract.second_contAux_eq
-/

#print GenContFract.first_cont_eq /-
theorem first_cont_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.conts 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [nth_cont_eq_succ_nth_cont_aux, second_continuant_aux_eq zeroth_s_eq]
#align generalized_continued_fraction.first_continuant_eq GenContFract.first_cont_eq
-/

#print GenContFract.first_num_eq /-
theorem first_num_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.nums 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_continuant_eq zeroth_s_eq]
#align generalized_continued_fraction.first_numerator_eq GenContFract.first_num_eq
-/

#print GenContFract.first_den_eq /-
theorem first_den_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) : g.dens 1 = gp.b := by
  simp [denom_eq_conts_b, first_continuant_eq zeroth_s_eq]
#align generalized_continued_fraction.first_denominator_eq GenContFract.first_den_eq
-/

#print GenContFract.zeroth_conv'Aux_eq_zero /-
@[simp]
theorem zeroth_conv'Aux_eq_zero {s : Seq <| Pair K} : convs'Aux s 0 = 0 :=
  rfl
#align generalized_continued_fraction.zeroth_convergent'_aux_eq_zero GenContFract.zeroth_conv'Aux_eq_zero
-/

#print GenContFract.zeroth_conv'_eq_h /-
@[simp]
theorem zeroth_conv'_eq_h : g.convs' 0 = g.h := by simp [convergents']
#align generalized_continued_fraction.zeroth_convergent'_eq_h GenContFract.zeroth_conv'_eq_h
-/

#print GenContFract.convs'Aux_succ_none /-
theorem convs'Aux_succ_none {s : Seq (Pair K)} (h : s.headI = none) (n : ℕ) :
    convs'Aux s (n + 1) = 0 := by rw [convergents'_aux, h, convergents'_aux._match_1]
#align generalized_continued_fraction.convergents'_aux_succ_none GenContFract.convs'Aux_succ_none
-/

#print GenContFract.convs'Aux_succ_some /-
theorem convs'Aux_succ_some {s : Seq (Pair K)} {p : Pair K} (h : s.headI = some p) (n : ℕ) :
    convs'Aux s (n + 1) = p.a / (p.b + convs'Aux s.tail n) := by
  rw [convergents'_aux, h, convergents'_aux._match_1]
#align generalized_continued_fraction.convergents'_aux_succ_some GenContFract.convs'Aux_succ_some
-/

end WithDivisionRing

end GenContFract

