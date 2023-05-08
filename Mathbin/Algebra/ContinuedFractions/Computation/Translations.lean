/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann

! This file was ported from Lean 3 source module algebra.continued_fractions.computation.translations
! leanprover-community/mathlib commit a7e36e48519ab281320c4d192da6a7b348ce40ad
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.ContinuedFractions.Computation.Basic
import Mathbin.Algebra.ContinuedFractions.Translations

/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `algebra.continued_fractions.computation.basic`. The file consists
of three sections:
1. Recurrences and inversion lemmas for `int_fract_pair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`int_fract_pair.stream`, `int_fract_pair.seq1`, and
   `generalized_continued_fraction.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `nth_of_eq_some_of_succ_nth_int_fract_pair_stream` and
  `nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/


namespace GeneralizedContinuedFraction

open GeneralizedContinuedFraction (of)

/- ./././Mathport/Syntax/Translate/Command.lean:229:11: unsupported: unusual advanced open style -/
-- Fix a discrete linear ordered floor field and a value `v`.
variable {K : Type _} [LinearOrderedField K] [FloorRing K] {v : K}

namespace IntFractPair

/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/


#print GeneralizedContinuedFraction.IntFractPair.stream_zero /-
theorem stream_zero (v : K) : IntFractPair.stream v 0 = some (IntFractPair.of v) :=
  rfl
#align generalized_continued_fraction.int_fract_pair.stream_zero GeneralizedContinuedFraction.IntFractPair.stream_zero
-/

variable {n : ℕ}

/- warning: generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero -> GeneralizedContinuedFraction.IntFractPair.stream_eq_none_of_fr_eq_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero GeneralizedContinuedFraction.IntFractPair.stream_eq_none_of_fr_eq_zeroₓ'. -/
theorem stream_eq_none_of_fr_eq_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
    IntFractPair.stream v (n + 1) = none :=
  by
  cases' ifp_n with _ fr
  change fr = 0 at nth_fr_eq_zero
  simp [int_fract_pair.stream, stream_nth_eq, nth_fr_eq_zero]
#align generalized_continued_fraction.int_fract_pair.stream_eq_none_of_fr_eq_zero GeneralizedContinuedFraction.IntFractPair.stream_eq_none_of_fr_eq_zero

/- warning: generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff -> GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_none_iff is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat}, Iff (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))) (Or (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))) (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp)) (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat}, Iff (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))) (Or (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))) (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp)) (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_none_iffₓ'. -/
/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
theorem succ_nth_stream_eq_none_iff :
    IntFractPair.stream v (n + 1) = none ↔
      IntFractPair.stream v n = none ∨ ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr = 0 :=
  by
  rw [int_fract_pair.stream]
  cases int_fract_pair.stream v n <;> simp [imp_false]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_none_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_none_iff

/- warning: generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff -> GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iff is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, Iff (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) (And (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) (Eq.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n))) ifp_succ_n))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, Iff (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) (And (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (Eq.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n))) ifp_succ_n))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iffₓ'. -/
/-- Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
theorem succ_nth_stream_eq_some_iff {ifp_succ_n : IntFractPair K} :
    IntFractPair.stream v (n + 1) = some ifp_succ_n ↔
      ∃ ifp_n : IntFractPair K,
        IntFractPair.stream v n = some ifp_n ∧
          ifp_n.fr ≠ 0 ∧ IntFractPair.of ifp_n.fr⁻¹ = ifp_succ_n :=
  by simp [int_fract_pair.stream, ite_eq_iff]
#align generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff GeneralizedContinuedFraction.IntFractPair.succ_nth_stream_eq_some_iff

/- warning: generalized_continued_fraction.int_fract_pair.stream_succ_of_some -> GeneralizedContinuedFraction.IntFractPair.stream_succ_of_some is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {p : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) p)) -> (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K p) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K p)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {p : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) p)) -> (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K p) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K p)))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.stream_succ_of_some GeneralizedContinuedFraction.IntFractPair.stream_succ_of_someₓ'. -/
/-- An easier to use version of one direction of
`generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff`.
-/
theorem stream_succ_of_some {p : IntFractPair K} (h : IntFractPair.stream v n = some p)
    (h' : p.fr ≠ 0) : IntFractPair.stream v (n + 1) = some (IntFractPair.of p.fr⁻¹) :=
  succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩
#align generalized_continued_fraction.int_fract_pair.stream_succ_of_some GeneralizedContinuedFraction.IntFractPair.stream_succ_of_some

/- warning: generalized_continued_fraction.int_fract_pair.stream_succ_of_int -> GeneralizedContinuedFraction.IntFractPair.stream_succ_of_int is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (a : Int) (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (a : Int) (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) a) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.none.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.stream_succ_of_int GeneralizedContinuedFraction.IntFractPair.stream_succ_of_intₓ'. -/
/-- The stream of `int_fract_pair`s of an integer stops after the first term.
-/
theorem stream_succ_of_int (a : ℤ) (n : ℕ) : IntFractPair.stream (a : K) (n + 1) = none :=
  by
  induction' n with n ih
  · refine' int_fract_pair.stream_eq_none_of_fr_eq_zero (int_fract_pair.stream_zero (a : K)) _
    simp only [int_fract_pair.of, Int.fract_intCast]
  · exact int_fract_pair.succ_nth_stream_eq_none_iff.mpr (Or.inl ih)
#align generalized_continued_fraction.int_fract_pair.stream_succ_of_int GeneralizedContinuedFraction.IntFractPair.stream_succ_of_int

/- warning: generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero -> GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_fr_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_succ_n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) (Eq.{succ u1} K (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n)))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) -> (Eq.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_succ_n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) (Eq.{succ u1} K (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n)) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n)))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_fr_zeroₓ'. -/
theorem exists_succ_nth_stream_of_fr_zero {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n)
    (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
    ∃ ifp_n : IntFractPair K, IntFractPair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
  by
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq with
    ⟨ifp_n, seq_nth_eq, nth_fr_ne_zero, rfl⟩
  refine' ⟨ifp_n, seq_nth_eq, _⟩
  simpa only [int_fract_pair.of, Int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_fr_zero GeneralizedContinuedFraction.IntFractPair.exists_succ_nth_stream_of_fr_zero

/- warning: generalized_continued_fraction.int_fract_pair.stream_succ -> GeneralizedContinuedFraction.IntFractPair.stream_succ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, (Ne.{succ u1} K (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (forall (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)) n))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, (Ne.{succ u1} K (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (forall (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)) n))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.stream_succ GeneralizedContinuedFraction.IntFractPair.stream_succₓ'. -/
/-- A recurrence relation that expresses the `(n+1)`th term of the stream of `int_fract_pair`s
of `v` for non-integer `v` in terms of the `n`th term of the stream associated to
the inverse of the fractional part of `v`.
-/
theorem stream_succ (h : Int.fract v ≠ 0) (n : ℕ) :
    IntFractPair.stream v (n + 1) = IntFractPair.stream (Int.fract v)⁻¹ n :=
  by
  induction' n with n ih
  · have H : (int_fract_pair.of v).fr = Int.fract v := rfl
    rw [stream_zero, stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h), H]
  · cases' eq_or_ne (int_fract_pair.stream (Int.fract v)⁻¹ n) none with hnone hsome
    · rw [hnone] at ih
      rw [succ_nth_stream_eq_none_iff.mpr (Or.inl hnone),
        succ_nth_stream_eq_none_iff.mpr (Or.inl ih)]
    · obtain ⟨p, hp⟩ := option.ne_none_iff_exists'.mp hsome
      rw [hp] at ih
      cases' eq_or_ne p.fr 0 with hz hnz
      · rw [stream_eq_none_of_fr_eq_zero hp hz, stream_eq_none_of_fr_eq_zero ih hz]
      · rw [stream_succ_of_some hp hnz, stream_succ_of_some ih hnz]
#align generalized_continued_fraction.int_fract_pair.stream_succ GeneralizedContinuedFraction.IntFractPair.stream_succ

end IntFractPair

section Head

/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/


#print GeneralizedContinuedFraction.IntFractPair.seq1_fst_eq_of /-
/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
theorem IntFractPair.seq1_fst_eq_of : (IntFractPair.seq1 v).fst = IntFractPair.of v :=
  rfl
#align generalized_continued_fraction.int_fract_pair.seq1_fst_eq_of GeneralizedContinuedFraction.IntFractPair.seq1_fst_eq_of
-/

/- warning: generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b -> GeneralizedContinuedFraction.of_h_eq_intFractPair_seq1_fst_b is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, Eq.{succ u1} K (GeneralizedContinuedFraction.h.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K (Prod.fst.{u1, u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (Stream'.Seq.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.seq1.{u1} K _inst_1 _inst_2 v))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, Eq.{succ u1} K (GeneralizedContinuedFraction.h.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K (Prod.fst.{u1, u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (Stream'.Seq.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.seq1.{u1} K _inst_1 _inst_2 v))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b GeneralizedContinuedFraction.of_h_eq_intFractPair_seq1_fst_bₓ'. -/
theorem of_h_eq_intFractPair_seq1_fst_b : (of v).h = (IntFractPair.seq1 v).fst.b :=
  by
  cases aux_seq_eq : int_fract_pair.seq1 v
  simp [of, aux_seq_eq]
#align generalized_continued_fraction.of_h_eq_int_fract_pair_seq1_fst_b GeneralizedContinuedFraction.of_h_eq_intFractPair_seq1_fst_b

/- warning: generalized_continued_fraction.of_h_eq_floor -> GeneralizedContinuedFraction.of_h_eq_floor is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, Eq.{succ u1} K (GeneralizedContinuedFraction.h.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, Eq.{succ u1} K (GeneralizedContinuedFraction.h.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_h_eq_floor GeneralizedContinuedFraction.of_h_eq_floorₓ'. -/
/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
theorem of_h_eq_floor : (of v).h = ⌊v⌋ := by
  simp [of_h_eq_int_fract_pair_seq1_fst_b, int_fract_pair.of]
#align generalized_continued_fraction.of_h_eq_floor GeneralizedContinuedFraction.of_h_eq_floor

end Head

section sequence

/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`int_fract_pair.stream`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/


variable {n : ℕ}

#print GeneralizedContinuedFraction.IntFractPair.get?_seq1_eq_succ_get?_stream /-
theorem IntFractPair.get?_seq1_eq_succ_get?_stream :
    (IntFractPair.seq1 v).snd.get? n = (IntFractPair.stream v) (n + 1) :=
  rfl
#align generalized_continued_fraction.int_fract_pair.nth_seq1_eq_succ_nth_stream GeneralizedContinuedFraction.IntFractPair.get?_seq1_eq_succ_get?_stream
-/

section Termination

/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/


#print GeneralizedContinuedFraction.of_terminatedAt_iff_intFractPair_seq1_terminatedAt /-
theorem of_terminatedAt_iff_intFractPair_seq1_terminatedAt :
    (of v).TerminatedAt n ↔ (IntFractPair.seq1 v).snd.TerminatedAt n :=
  Option.map_eq_none
#align generalized_continued_fraction.of_terminated_at_iff_int_fract_pair_seq1_terminated_at GeneralizedContinuedFraction.of_terminatedAt_iff_intFractPair_seq1_terminatedAt
-/

#print GeneralizedContinuedFraction.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none /-
theorem of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none :
    (of v).TerminatedAt n ↔ IntFractPair.stream v (n + 1) = none := by
  rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, Stream'.Seq.TerminatedAt,
    int_fract_pair.nth_seq1_eq_succ_nth_stream]
#align generalized_continued_fraction.of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none GeneralizedContinuedFraction.of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none
-/

end Termination

section Values

/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/


/- warning: generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some -> GeneralizedContinuedFraction.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {gp_n : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp_n)) -> (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp)) (Eq.{succ u1} K ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K ifp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp_n))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {gp_n : GeneralizedContinuedFraction.Pair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) gp_n)) -> (Exists.{succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (fun (ifp : GeneralizedContinuedFraction.IntFractPair.{u1} K) => And (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp)) (Eq.{succ u1} K (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K ifp)) (GeneralizedContinuedFraction.Pair.b.{u1} K gp_n))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some GeneralizedContinuedFraction.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_someₓ'. -/
theorem IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some {gp_n : Pair K}
    (s_nth_eq : (of v).s.get? n = some gp_n) :
    ∃ ifp : IntFractPair K, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
  by
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ pair.mk 1 (ifp.b : K) = gp_n :=
    by
    unfold of int_fract_pair.seq1 at s_nth_eq
    rwa [seq.map_tail, seq.nth_tail, seq.map_nth, Option.map_eq_some'] at s_nth_eq
  cases gp_n_eq
  injection gp_n_eq with _ ifp_b_eq_gp_n_b
  exists ifp
  exact ⟨stream_succ_nth_eq, ifp_b_eq_gp_n_b⟩
#align generalized_continued_fraction.int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some GeneralizedContinuedFraction.IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some

/- warning: generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream -> GeneralizedContinuedFraction.get?_of_eq_some_of_succ_get?_intFractPair_stream is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K ifp_succ_n)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_succ_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_succ_n)) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (StrictOrderedSemiring.toSemiring.{u1} K (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} K (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} K (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K ifp_succ_n)))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream GeneralizedContinuedFraction.get?_of_eq_some_of_succ_get?_intFractPair_streamₓ'. -/
/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_succ_get?_intFractPair_stream {ifp_succ_n : IntFractPair K}
    (stream_succ_nth_eq : IntFractPair.stream v (n + 1) = some ifp_succ_n) :
    (of v).s.get? n = some ⟨1, ifp_succ_n.b⟩ :=
  by
  unfold of int_fract_pair.seq1
  rw [seq.map_tail, seq.nth_tail, seq.map_nth]
  simp [seq.nth, stream_succ_nth_eq]
#align generalized_continued_fraction.nth_of_eq_some_of_succ_nth_int_fract_pair_stream GeneralizedContinuedFraction.get?_of_eq_some_of_succ_get?_intFractPair_stream

/- warning: generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero -> GeneralizedContinuedFraction.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) -> (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n))))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K} {n : Nat} {ifp_n : GeneralizedContinuedFraction.IntFractPair.{u1} K}, (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K)) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v n) (Option.some.{u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) ifp_n)) -> (Ne.{succ u1} K (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) n) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (StrictOrderedSemiring.toSemiring.{u1} K (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} K (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} K (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K (GeneralizedContinuedFraction.IntFractPair.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (GeneralizedContinuedFraction.IntFractPair.fr.{u1} K ifp_n))))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero GeneralizedContinuedFraction.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zeroₓ'. -/
/-- Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
theorem get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero {ifp_n : IntFractPair K}
    (stream_nth_eq : IntFractPair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
    (of v).s.get? n = some ⟨1, (IntFractPair.of ifp_n.fr⁻¹).b⟩ :=
  have : IntFractPair.stream v (n + 1) = some (IntFractPair.of ifp_n.fr⁻¹) :=
    by
    cases ifp_n
    simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero]
  get?_of_eq_some_of_succ_get?_intFractPair_stream this
#align generalized_continued_fraction.nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero GeneralizedContinuedFraction.get?_of_eq_some_of_get?_intFractPair_stream_fr_ne_zero

open Int IntFractPair

/- warning: generalized_continued_fraction.of_s_head_aux -> GeneralizedContinuedFraction.of_s_head_aux is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Option.bind.{u1, u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) (Function.comp.{succ u1, succ u1, succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.Pair.{u1} K) (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (fun (p : GeneralizedContinuedFraction.IntFractPair.{u1} K) => GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K p)))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Option.bind.{u1, u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.IntFractPair.stream.{u1} K _inst_1 _inst_2 v (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) (Function.comp.{succ u1, succ u1, succ u1} (GeneralizedContinuedFraction.IntFractPair.{u1} K) (GeneralizedContinuedFraction.Pair.{u1} K) (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (fun (p : GeneralizedContinuedFraction.IntFractPair.{u1} K) => GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (StrictOrderedSemiring.toSemiring.{u1} K (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} K (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} K (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (GeneralizedContinuedFraction.IntFractPair.b.{u1} K p)))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_s_head_aux GeneralizedContinuedFraction.of_s_head_auxₓ'. -/
theorem of_s_head_aux (v : K) :
    (of v).s.get? 0 =
      (IntFractPair.stream v 1).bind
        (some ∘ fun p =>
          { a := 1
            b := p.b }) :=
  by
  rw [of, int_fract_pair.seq1, of._match_1]
  simp only [seq.map_tail, seq.map, seq.tail, seq.head, seq.nth, Stream'.map]
  rw [← Stream'.nth_succ, Stream'.nth, Option.map]
#align generalized_continued_fraction.of_s_head_aux GeneralizedContinuedFraction.of_s_head_aux

/- warning: generalized_continued_fraction.of_s_head -> GeneralizedContinuedFraction.of_s_head is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, (Ne.{succ u1} K (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v) (OfNat.ofNat.{u1} K 0 (OfNat.mk.{u1} K 0 (Zero.zero.{u1} K (MulZeroClass.toHasZero.{u1} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)))))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] {v : K}, (Ne.{succ u1} K (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v) (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (LinearOrderedSemifield.toSemifield.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) -> (Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.head.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v))) (Option.some.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.Pair.mk.{u1} K (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (StrictOrderedSemiring.toSemiring.{u1} K (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} K (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} K (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)))))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_s_head GeneralizedContinuedFraction.of_s_headₓ'. -/
/-- This gives the first pair of coefficients of the continued fraction of a non-integer `v`.
-/
theorem of_s_head (h : fract v ≠ 0) : (of v).s.headI = some ⟨1, ⌊(fract v)⁻¹⌋⟩ :=
  by
  change (of v).s.get? 0 = _
  rw [of_s_head_aux, stream_succ_of_some (stream_zero v) h, Option.bind]
  rfl
#align generalized_continued_fraction.of_s_head GeneralizedContinuedFraction.of_s_head

variable (K)

/- warning: generalized_continued_fraction.of_s_of_int -> GeneralizedContinuedFraction.of_s_of_int is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (a : Int), Eq.{succ u1} (Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) a))) (Stream'.Seq.nil.{u1} (GeneralizedContinuedFraction.Pair.{u1} K))
but is expected to have type
  forall (K : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (a : Int), Eq.{succ u1} (Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) a))) (Stream'.Seq.nil.{u1} (GeneralizedContinuedFraction.Pair.{u1} K))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_s_of_int GeneralizedContinuedFraction.of_s_of_intₓ'. -/
/-- If `a` is an integer, then the coefficient sequence of its continued fraction is empty.
-/
theorem of_s_of_int (a : ℤ) : (of (a : K)).s = Seq.nil :=
  haveI h : ∀ n, (of (a : K)).s.get? n = none :=
    by
    intro n
    induction' n with n ih
    · rw [of_s_head_aux, stream_succ_of_int, Option.bind]
    · exact (of (a : K)).s.Prop ih
  seq.ext fun n => (h n).trans (seq.nth_nil n).symm
#align generalized_continued_fraction.of_s_of_int GeneralizedContinuedFraction.of_s_of_int

variable {K} (v)

/- warning: generalized_continued_fraction.of_s_succ -> GeneralizedContinuedFraction.of_s_succ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K) (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)))) n)
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K) (n : Nat), Eq.{succ u1} (Option.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v)) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (Stream'.Seq.get?.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)))) n)
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_s_succ GeneralizedContinuedFraction.of_s_succₓ'. -/
/-- Recurrence for the `generalized_continued_fraction.of` an element `v` of `K` in terms of
that of the inverse of the fractional part of `v`.
-/
theorem of_s_succ (n : ℕ) : (of v).s.get? (n + 1) = (of (fract v)⁻¹).s.get? n :=
  by
  cases' eq_or_ne (fract v) 0 with h h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [fract_int_cast, inv_zero, of_s_of_int, ← cast_zero, of_s_of_int, seq.nth_nil, seq.nth_nil]
  cases' eq_or_ne ((of (fract v)⁻¹).s.get? n) none with h₁ h₁
  ·
    rwa [h₁, ← terminated_at_iff_s_none,
      of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none, stream_succ h, ←
      of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none, terminated_at_iff_s_none]
  · obtain ⟨p, hp⟩ := option.ne_none_iff_exists'.mp h₁
    obtain ⟨p', hp'₁, _⟩ := exists_succ_nth_stream_of_gcf_of_nth_eq_some hp
    have Hp := nth_of_eq_some_of_succ_nth_int_fract_pair_stream hp'₁
    rw [← stream_succ h] at hp'₁
    rw [Hp, nth_of_eq_some_of_succ_nth_int_fract_pair_stream hp'₁]
#align generalized_continued_fraction.of_s_succ GeneralizedContinuedFraction.of_s_succ

/- warning: generalized_continued_fraction.of_s_tail -> GeneralizedContinuedFraction.of_s_tail is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K), Eq.{succ u1} (Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.tail.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v))) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K), Eq.{succ u1} (Stream'.Seq.{u1} (GeneralizedContinuedFraction.Pair.{u1} K)) (Stream'.Seq.tail.{u1} (GeneralizedContinuedFraction.Pair.{u1} K) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v))) (GeneralizedContinuedFraction.s.{u1} K (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.of_s_tail GeneralizedContinuedFraction.of_s_tailₓ'. -/
/-- This expresses the tail of the coefficient sequence of the `generalized_continued_fraction.of`
an element `v` of `K` as the coefficient sequence of that of the inverse of the
fractional part of `v`.
-/
theorem of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
  Seq.ext fun n => Seq.get?_tail (of v).s n ▸ of_s_succ v n
#align generalized_continued_fraction.of_s_tail GeneralizedContinuedFraction.of_s_tail

variable (K) (n)

/- warning: generalized_continued_fraction.convergents'_of_int -> GeneralizedContinuedFraction.convergents'_of_int is a dubious translation:
lean 3 declaration is
  forall (K : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (n : Nat) (a : Int), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) a)) n) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) a)
but is expected to have type
  forall (K : Type.{u1}) [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (n : Nat) (a : Int), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) a)) n) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) a)
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergents'_of_int GeneralizedContinuedFraction.convergents'_of_intₓ'. -/
/-- If `a` is an integer, then the `convergents'` of its continued fraction expansion
are all equal to `a`.
-/
theorem convergents'_of_int (a : ℤ) : (of (a : K)).convergents' n = a :=
  by
  induction' n with n ih
  · simp only [zeroth_convergent'_eq_h, of_h_eq_floor, floor_int_cast]
  · rw [convergents', of_h_eq_floor, floor_int_cast, add_right_eq_self]
    exact convergents'_aux_succ_none ((of_s_of_int K a).symm ▸ seq.nth_nil 0) _
#align generalized_continued_fraction.convergents'_of_int GeneralizedContinuedFraction.convergents'_of_int

variable {K} (v)

/- warning: generalized_continued_fraction.convergents'_succ -> GeneralizedContinuedFraction.convergents'_succ is a dubious translation:
lean 3 declaration is
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K) (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toHasAdd.{u1} K (Ring.toDistrib.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Int K (HasLiftT.mk.{1, succ u1} Int K (CoeTCₓ.coe.{1, succ u1} Int K (Int.castCoe.{u1} K (AddGroupWithOne.toHasIntCast.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (DivInvMonoid.toHasDiv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1))))) (OfNat.ofNat.{u1} K 1 (OfNat.mk.{u1} K 1 (One.one.{u1} K (AddMonoidWithOne.toOne.{u1} K (AddGroupWithOne.toAddMonoidWithOne.{u1} K (AddCommGroupWithOne.toAddGroupWithOne.{u1} K (Ring.toAddCommGroupWithOne.{u1} K (DivisionRing.toRing.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))))))))) (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (DivInvMonoid.toHasInv.{u1} K (DivisionRing.toDivInvMonoid.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)))) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))) n)))
but is expected to have type
  forall {K : Type.{u1}} [_inst_1 : LinearOrderedField.{u1} K] [_inst_2 : FloorRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))] (v : K) (n : Nat), Eq.{succ u1} K (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 v) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (HAdd.hAdd.{u1, u1, u1} K K K (instHAdd.{u1} K (Distrib.toAdd.{u1} K (NonUnitalNonAssocSemiring.toDistrib.{u1} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} K (NonAssocRing.toNonUnitalNonAssocRing.{u1} K (Ring.toNonAssocRing.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)))))))))) (Int.cast.{u1} K (Ring.toIntCast.{u1} K (StrictOrderedRing.toRing.{u1} K (LinearOrderedRing.toStrictOrderedRing.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1))))) (Int.floor.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v)) (HDiv.hDiv.{u1, u1, u1} K K K (instHDiv.{u1} K (LinearOrderedField.toDiv.{u1} K _inst_1)) (OfNat.ofNat.{u1} K 1 (One.toOfNat1.{u1} K (Semiring.toOne.{u1} K (StrictOrderedSemiring.toSemiring.{u1} K (LinearOrderedSemiring.toStrictOrderedSemiring.{u1} K (LinearOrderedCommSemiring.toLinearOrderedSemiring.{u1} K (LinearOrderedSemifield.toLinearOrderedCommSemiring.{u1} K (LinearOrderedField.toLinearOrderedSemifield.{u1} K _inst_1)))))))) (GeneralizedContinuedFraction.convergents'.{u1} K (Field.toDivisionRing.{u1} K (LinearOrderedField.toField.{u1} K _inst_1)) (GeneralizedContinuedFraction.of.{u1} K _inst_1 _inst_2 (Inv.inv.{u1} K (LinearOrderedField.toInv.{u1} K _inst_1) (Int.fract.{u1} K (LinearOrderedCommRing.toLinearOrderedRing.{u1} K (LinearOrderedField.toLinearOrderedCommRing.{u1} K _inst_1)) _inst_2 v))) n)))
Case conversion may be inaccurate. Consider using '#align generalized_continued_fraction.convergents'_succ GeneralizedContinuedFraction.convergents'_succₓ'. -/
/-- The recurrence relation for the `convergents'` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
theorem convergents'_succ :
    (of v).convergents' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convergents' n :=
  by
  cases' eq_or_ne (fract v) 0 with h h
  · obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩
    rw [convergents'_of_int, fract_int_cast, inv_zero, ← cast_zero, convergents'_of_int, cast_zero,
      div_zero, add_zero, floor_int_cast]
  · rw [convergents', of_h_eq_floor, add_right_inj, convergents'_aux_succ_some (of_s_head h)]
    exact congr_arg ((· / ·) 1) (by rw [convergents', of_h_eq_floor, add_right_inj, of_s_tail])
#align generalized_continued_fraction.convergents'_succ GeneralizedContinuedFraction.convergents'_succ

end Values

end sequence

end GeneralizedContinuedFraction

