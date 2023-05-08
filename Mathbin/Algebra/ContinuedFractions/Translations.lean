/-
Copyright (c) 2019 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann

! This file was ported from Lean 3 source module algebra.continued_fractions.translations
! leanprover-community/mathlib commit b5ad141426bb005414324f89719c77c0aa3ec612
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.ContinuedFractions.Basic

/-!
# Basic Translation Lemmas Between Functions Defined for Continued Fractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

Some simple translation lemmas between the different definitions of functions defined in
`algebra.continued_fractions.basic`.
-/


namespace GeneralizedContinuedFraction

/- ./././Mathport/Syntax/Translate/Command.lean:229:11: unsupported: unusual advanced open style -/
section General

/-!
### Translations Between General Access Functions

Here we give some basic translations that hold by definition between the various methods that allow
us to access the numerators and denominators of a continued fraction.
-/


variable {α : Type _} {g : GeneralizedContinuedFraction α} {n : ℕ}

#print GeneralizedContinuedFraction.terminatedAt_iff_s_terminatedAt /-
theorem terminatedAt_iff_s_terminatedAt : g.TerminatedAt n ↔ g.s.TerminatedAt n := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_terminated_at GeneralizedContinuedFraction.terminatedAt_iff_s_terminatedAt
-/

#print GeneralizedContinuedFraction.terminatedAt_iff_s_none /-
theorem terminatedAt_iff_s_none : g.TerminatedAt n ↔ g.s.get? n = none := by rfl
#align generalized_continued_fraction.terminated_at_iff_s_none GeneralizedContinuedFraction.terminatedAt_iff_s_none
-/

#print GeneralizedContinuedFraction.part_num_none_iff_s_none /-
theorem part_num_none_iff_s_none : g.partialNumerators.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [partial_numerators, s_nth_eq]
#align generalized_continued_fraction.part_num_none_iff_s_none GeneralizedContinuedFraction.part_num_none_iff_s_none
-/

#print GeneralizedContinuedFraction.terminatedAt_iff_part_num_none /-
theorem terminatedAt_iff_part_num_none : g.TerminatedAt n ↔ g.partialNumerators.get? n = none := by
  rw [terminated_at_iff_s_none, part_num_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_num_none GeneralizedContinuedFraction.terminatedAt_iff_part_num_none
-/

#print GeneralizedContinuedFraction.part_denom_none_iff_s_none /-
theorem part_denom_none_iff_s_none : g.partialDenominators.get? n = none ↔ g.s.get? n = none := by
  cases s_nth_eq : g.s.nth n <;> simp [partial_denominators, s_nth_eq]
#align generalized_continued_fraction.part_denom_none_iff_s_none GeneralizedContinuedFraction.part_denom_none_iff_s_none
-/

#print GeneralizedContinuedFraction.terminatedAt_iff_part_denom_none /-
theorem terminatedAt_iff_part_denom_none : g.TerminatedAt n ↔ g.partialDenominators.get? n = none :=
  by rw [terminated_at_iff_s_none, part_denom_none_iff_s_none]
#align generalized_continued_fraction.terminated_at_iff_part_denom_none GeneralizedContinuedFraction.terminatedAt_iff_part_denom_none
-/

#print GeneralizedContinuedFraction.part_num_eq_s_a /-
theorem part_num_eq_s_a {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partialNumerators.get? n = some gp.a := by simp [partial_numerators, s_nth_eq]
#align generalized_continued_fraction.part_num_eq_s_a GeneralizedContinuedFraction.part_num_eq_s_a
-/

#print GeneralizedContinuedFraction.part_denom_eq_s_b /-
theorem part_denom_eq_s_b {gp : Pair α} (s_nth_eq : g.s.get? n = some gp) :
    g.partialDenominators.get? n = some gp.b := by simp [partial_denominators, s_nth_eq]
#align generalized_continued_fraction.part_denom_eq_s_b GeneralizedContinuedFraction.part_denom_eq_s_b
-/

#print GeneralizedContinuedFraction.exists_s_a_of_part_num /-
theorem exists_s_a_of_part_num {a : α} (nth_part_num_eq : g.partialNumerators.get? n = some a) :
    ∃ gp, g.s.get? n = some gp ∧ gp.a = a := by
  simpa [partial_numerators, seq.map_nth] using nth_part_num_eq
#align generalized_continued_fraction.exists_s_a_of_part_num GeneralizedContinuedFraction.exists_s_a_of_part_num
-/

#print GeneralizedContinuedFraction.exists_s_b_of_part_denom /-
theorem exists_s_b_of_part_denom {b : α}
    (nth_part_denom_eq : g.partialDenominators.get? n = some b) :
    ∃ gp, g.s.get? n = some gp ∧ gp.b = b := by
  simpa [partial_denominators, seq.map_nth] using nth_part_denom_eq
#align generalized_continued_fraction.exists_s_b_of_part_denom GeneralizedContinuedFraction.exists_s_b_of_part_denom
-/

end General

section WithDivisionRing

/-!
### Translations Between Computational Functions

Here we  give some basic translations that hold by definition for the computational methods of a
continued fraction.
-/


variable {K : Type _} {g : GeneralizedContinuedFraction K} {n : ℕ} [DivisionRing K]

#print GeneralizedContinuedFraction.nth_cont_eq_succ_nth_cont_aux /-
theorem nth_cont_eq_succ_nth_cont_aux : g.continuants n = g.continuantsAux (n + 1) :=
  rfl
#align generalized_continued_fraction.nth_cont_eq_succ_nth_cont_aux GeneralizedContinuedFraction.nth_cont_eq_succ_nth_cont_aux
-/

#print GeneralizedContinuedFraction.num_eq_conts_a /-
theorem num_eq_conts_a : g.numerators n = (g.continuants n).a :=
  rfl
#align generalized_continued_fraction.num_eq_conts_a GeneralizedContinuedFraction.num_eq_conts_a
-/

#print GeneralizedContinuedFraction.denom_eq_conts_b /-
theorem denom_eq_conts_b : g.denominators n = (g.continuants n).b :=
  rfl
#align generalized_continued_fraction.denom_eq_conts_b GeneralizedContinuedFraction.denom_eq_conts_b
-/

/- warning: generalized_continued_fraction.convergent_eq_num_div_denom -> GeneralizedContinuedFraction.convergent_eq_num_div_denom is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} {n : Nat} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.convergents.{u1} K _inst_1 g n) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivInvMonoid.toHasDiv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_1))) (GeneralizedContinuedFraction.numerators.{u1} K _inst_1 g n) (GeneralizedContinuedFraction.denominators.{u1} K _inst_1 g n))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} {n : Nat} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.convergents.{u1} K _inst_1 g n) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivisionRing.toDiv.{u1} K _inst_1)) (GeneralizedContinuedFraction.numerators.{u1} K _inst_1 g n) (GeneralizedContinuedFraction.denominators.{u1} K _inst_1 g n))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergent_eq_num_div_denom GeneralizedContinuedFraction.convergent_eq_num_div_denomₓ'. -/
theorem convergent_eq_num_div_denom : g.convergents n = g.numerators n / g.denominators n :=
  rfl
#align generalized_continued_fraction.convergent_eq_num_div_denom GeneralizedContinuedFraction.convergent_eq_num_div_denom

/- warning: generalized_continued_fraction.convergent_eq_conts_a_div_conts_b -> GeneralizedContinuedFraction.convergent_eq_conts_a_div_conts_b is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} {n : Nat} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.convergents.{u1} K _inst_1 g n) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivInvMonoid.toHasDiv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_1))) (GeneralizedContinuedFraction.Pair.a.{u1} K (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g n)) (GeneralizedContinuedFraction.Pair.b.{u1} K (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g n)))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} {n : Nat} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.convergents.{u1} K _inst_1 g n) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivisionRing.toDiv.{u1} K _inst_1)) (GeneralizedContinuedFraction.Pair.a.{u1} K (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g n)) (GeneralizedContinuedFraction.Pair.b.{u1} K (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g n)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergent_eq_conts_a_div_conts_b GeneralizedContinuedFraction.convergent_eq_conts_a_div_conts_bₓ'. -/
theorem convergent_eq_conts_a_div_conts_b :
    g.convergents n = (g.continuants n).a / (g.continuants n).b :=
  rfl
#align generalized_continued_fraction.convergent_eq_conts_a_div_conts_b GeneralizedContinuedFraction.convergent_eq_conts_a_div_conts_b

#print GeneralizedContinuedFraction.exists_conts_a_of_num /-
theorem exists_conts_a_of_num {A : K} (nth_num_eq : g.numerators n = A) :
    ∃ conts, g.continuants n = conts ∧ conts.a = A := by simpa
#align generalized_continued_fraction.exists_conts_a_of_num GeneralizedContinuedFraction.exists_conts_a_of_num
-/

#print GeneralizedContinuedFraction.exists_conts_b_of_denom /-
theorem exists_conts_b_of_denom {B : K} (nth_denom_eq : g.denominators n = B) :
    ∃ conts, g.continuants n = conts ∧ conts.b = B := by simpa
#align generalized_continued_fraction.exists_conts_b_of_denom GeneralizedContinuedFraction.exists_conts_b_of_denom
-/

/- warning: generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero -> GeneralizedContinuedFraction.zeroth_continuant_aux_eq_one_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))))))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero GeneralizedContinuedFraction.zeroth_continuant_aux_eq_one_zeroₓ'. -/
@[simp]
theorem zeroth_continuant_aux_eq_one_zero : g.continuantsAux 0 = ⟨1, 0⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_aux_eq_one_zero GeneralizedContinuedFraction.zeroth_continuant_aux_eq_one_zero

/- warning: generalized_continued_fraction.first_continuant_aux_eq_h_one -> GeneralizedContinuedFraction.first_continuant_aux_eq_h_one is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (GeneralizedContinuedFraction.h.{u1} K g) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (GeneralizedContinuedFraction.h.{u1} K g) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.first_continuant_aux_eq_h_one GeneralizedContinuedFraction.first_continuant_aux_eq_h_oneₓ'. -/
@[simp]
theorem first_continuant_aux_eq_h_one : g.continuantsAux 1 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.first_continuant_aux_eq_h_one GeneralizedContinuedFraction.first_continuant_aux_eq_h_one

/- warning: generalized_continued_fraction.zeroth_continuant_eq_h_one -> GeneralizedContinuedFraction.zeroth_continuant_eq_h_one is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (GeneralizedContinuedFraction.h.{u1} K g) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (GeneralizedContinuedFraction.h.{u1} K g) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.zeroth_continuant_eq_h_one GeneralizedContinuedFraction.zeroth_continuant_eq_h_oneₓ'. -/
@[simp]
theorem zeroth_continuant_eq_h_one : g.continuants 0 = ⟨g.h, 1⟩ :=
  rfl
#align generalized_continued_fraction.zeroth_continuant_eq_h_one GeneralizedContinuedFraction.zeroth_continuant_eq_h_one

#print GeneralizedContinuedFraction.zeroth_numerator_eq_h /-
@[simp]
theorem zeroth_numerator_eq_h : g.numerators 0 = g.h :=
  rfl
#align generalized_continued_fraction.zeroth_numerator_eq_h GeneralizedContinuedFraction.zeroth_numerator_eq_h
-/

/- warning: generalized_continued_fraction.zeroth_denominator_eq_one -> GeneralizedContinuedFraction.zeroth_denominator_eq_one is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.denominators.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K], Eq.{succ u1} K (GeneralizedContinuedFraction.denominators.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.zeroth_denominator_eq_one GeneralizedContinuedFraction.zeroth_denominator_eq_oneₓ'. -/
@[simp]
theorem zeroth_denominator_eq_one : g.denominators 0 = 1 :=
  rfl
#align generalized_continued_fraction.zeroth_denominator_eq_one GeneralizedContinuedFraction.zeroth_denominator_eq_one

#print GeneralizedContinuedFraction.zeroth_convergent_eq_h /-
@[simp]
theorem zeroth_convergent_eq_h : g.convergents 0 = g.h := by
  simp [convergent_eq_num_div_denom, num_eq_conts_a, denom_eq_conts_b, div_one]
#align generalized_continued_fraction.zeroth_convergent_eq_h GeneralizedContinuedFraction.zeroth_convergent_eq_h
-/

/- warning: generalized_continued_fraction.second_continuant_aux_eq -> GeneralizedContinuedFraction.second_continuant_aux_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp)))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuantsAux.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toAdd.{u1} K (NonUnitalNonAssocSemiring.toDistrib.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.second_continuant_aux_eq GeneralizedContinuedFraction.second_continuant_aux_eqₓ'. -/
theorem second_continuant_aux_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.continuantsAux 2 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [zeroth_s_eq, continuants_aux, next_continuants, next_denominator, next_numerator]
#align generalized_continued_fraction.second_continuant_aux_eq GeneralizedContinuedFraction.second_continuant_aux_eq

/- warning: generalized_continued_fraction.first_continuant_eq -> GeneralizedContinuedFraction.first_continuant_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp)))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.continuants.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (GeneralizedContinuedFraction.Pair.mk.{u1} K (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toAdd.{u1} K (NonUnitalNonAssocSemiring.toDistrib.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.first_continuant_eq GeneralizedContinuedFraction.first_continuant_eqₓ'. -/
theorem first_continuant_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.continuants 1 = ⟨gp.b * g.h + gp.a, gp.b⟩ := by
  simp [nth_cont_eq_succ_nth_cont_aux, second_continuant_aux_eq zeroth_s_eq]
#align generalized_continued_fraction.first_continuant_eq GeneralizedContinuedFraction.first_continuant_eq

/- warning: generalized_continued_fraction.first_numerator_eq -> GeneralizedContinuedFraction.first_numerator_eq is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.numerators.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (Distrib.toHasMul.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)))
but is expected to have type
  forall {K : Type.{u1}} {g : GeneralizedContinuedFraction.{u1} K} [_inst_1 : DivisionRing.{u1} K] {gp : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K g) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.numerators.{u1} K _inst_1 g (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toAdd.{u1} K (NonUnitalNonAssocSemiring.toDistrib.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (HMul.hMul.{u1, u1, u1} K K K (instHMul.{u1} K (NonUnitalNonAssocRing.toMul.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.Pair.b.{u1} K gp) (GeneralizedContinuedFraction.h.{u1} K g)) (GeneralizedContinuedFraction.Pair.a.{u1} K gp)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.first_numerator_eq GeneralizedContinuedFraction.first_numerator_eqₓ'. -/
theorem first_numerator_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.numerators 1 = gp.b * g.h + gp.a := by simp [num_eq_conts_a, first_continuant_eq zeroth_s_eq]
#align generalized_continued_fraction.first_numerator_eq GeneralizedContinuedFraction.first_numerator_eq

#print GeneralizedContinuedFraction.first_denominator_eq /-
theorem first_denominator_eq {gp : Pair K} (zeroth_s_eq : g.s.get? 0 = some gp) :
    g.denominators 1 = gp.b := by simp [denom_eq_conts_b, first_continuant_eq zeroth_s_eq]
#align generalized_continued_fraction.first_denominator_eq GeneralizedContinuedFraction.first_denominator_eq
-/

/- warning: generalized_continued_fraction.zeroth_convergent'_aux_eq_zero -> GeneralizedContinuedFraction.zeroth_convergent'_aux_eq_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)}, Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)}, Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.zeroth_convergent'_aux_eq_zero GeneralizedContinuedFraction.zeroth_convergent'_aux_eq_zeroₓ'. -/
@[simp]
theorem zeroth_convergent'_aux_eq_zero {s : Seq <| Pair K} : convergents'Aux s 0 = 0 :=
  rfl
#align generalized_continued_fraction.zeroth_convergent'_aux_eq_zero GeneralizedContinuedFraction.zeroth_convergent'_aux_eq_zero

#print GeneralizedContinuedFraction.zeroth_convergent'_eq_h /-
@[simp]
theorem zeroth_convergent'_eq_h : g.convergents' 0 = g.h := by simp [convergents']
#align generalized_continued_fraction.zeroth_convergent'_eq_h GeneralizedContinuedFraction.zeroth_convergent'_eq_h
-/

/- warning: generalized_continued_fraction.convergents'_aux_succ_none -> GeneralizedContinuedFraction.convergents'Aux_succ_none is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) (Option.none.{u1} (GeneralizedContinuedFraction.Pair.{u1} K))) -> (forall (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) (Option.none.{u1} (GeneralizedContinuedFraction.Pair.{u1} K))) -> (forall (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (MonoidWithZero.toZero.{u1} K (Semiring.toMonoidWithZero.{u1} K (DivisionSemiring.toSemiring.{u1} K (DivisionRing.toDivisionSemiring.{u1} K _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergents'_aux_succ_none GeneralizedContinuedFraction.convergents'Aux_succ_noneₓ'. -/
theorem convergents'Aux_succ_none {s : Seq (Pair K)} (h : s.headI = none) (n : ℕ) :
    convergents'Aux s (n + 1) = 0 := by rw [convergents'_aux, h, convergents'_aux._match_1]
#align generalized_continued_fraction.convergents'_aux_succ_none GeneralizedContinuedFraction.convergents'Aux_succ_none

/- warning: generalized_continued_fraction.convergents'_aux_succ_some -> GeneralizedContinuedFraction.convergents'Aux_succ_some is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)} {p : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) p)) -> (forall (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivInvMonoid.toHasDiv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K _inst_1))) (GeneralizedContinuedFraction.Pair.a.{u1} K p) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K _inst_1)))) (GeneralizedContinuedFraction.Pair.b.{u1} K p) (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 (Stream'.Seq.tail.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) n))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : DivisionRing.{u1} K] {s : Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)} {p : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) p)) -> (forall (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 s (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivisionRing.toDiv.{u1} K _inst_1)) (GeneralizedContinuedFraction.Pair.a.{u1} K p) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toAdd.{u1} K (NonUnitalNonAssocSemiring.toDistrib.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K _inst_1))))))) (GeneralizedContinuedFraction.Pair.b.{u1} K p) (GeneralizedContinuedFraction.convergents'Aux.{u1} K _inst_1 (Stream'.Seq.tail.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) s) n))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergents'_aux_succ_some GeneralizedContinuedFraction.convergents'Aux_succ_someₓ'. -/
theorem convergents'Aux_succ_some {s : Seq (Pair K)} {p : Pair K} (h : s.headI = some p) (n : ℕ) :
    convergents'Aux s (n + 1) = p.a / (p.b + convergents'Aux s.tail n) := by
  rw [convergents'_aux, h, convergents'_aux._match_1]
#align generalized_continued_fraction.convergents'_aux_succ_some GeneralizedContinuedFraction.convergents'Aux_succ_some

end WithDivisionRing

end GeneralizedContinuedFraction

