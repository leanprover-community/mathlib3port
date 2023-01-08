/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro

! This file was ported from Lean 3 source module data.int.least_greatest
! leanprover-community/mathlib commit 940d371319c6658e526349d2c3e1daeeabfae0fd
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Int.Order.Basic

/-! # Least upper bound and greatest lower bound properties for integers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we prove that a bounded above nonempty set of integers has the greatest element, and a
counterpart of this statement for the least element.

## Main definitions

* `int.least_of_bdd`: if `P : ℤ → Prop` is a decidable predicate, `b` is a lower bound of the set
  `{m | P m}`, and there exists `m : ℤ` such that `P m` (this time, no witness is required), then
  `int.least_of_bdd` returns the least number `m` such that `P m`, together with proofs of `P m` and
  of the minimality. This definition is computable and does not rely on the axiom of choice.
* `int.greatest_of_bdd`: a similar definition with all inequalities reversed.

## Main statements

* `int.exists_least_of_bdd`: if `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is
  bounded below and nonempty, then this set has the least element. This lemma uses classical logic
  to avoid assumption `[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart.

* `int.coe_least_of_bdd_eq`: `(int.least_of_bdd b Hb Hinh : ℤ)` does not depend on `b`.

* `int.exists_greatest_of_bdd`, `int.coe_greatest_of_bdd_eq`: versions of the above lemmas with all
  inequalities reversed.

## Tags

integer numbers, least element, greatest element
-/


namespace Int

#print Int.leastOfBdd /-
/-- A computable version of `exists_least_of_bdd`: given a decidable predicate on the
integers, with an explicit lower bound and a proof that it is somewhere true, return
the least value for which the predicate is true. -/
def leastOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : { lb : ℤ // P lb ∧ ∀ z : ℤ, P z → lb ≤ z } :=
  have EX : ∃ n : ℕ, P (b + n) :=
    let ⟨elt, Helt⟩ := Hinh
    match elt, le.dest (Hb _ Helt), Helt with
    | _, ⟨n, rfl⟩, Hn => ⟨n, Hn⟩
  ⟨b + (Nat.find EX : ℤ), Nat.find_spec EX, fun z h =>
    match z, le.dest (Hb _ h), h with
    | _, ⟨n, rfl⟩, h => add_le_add_left (Int.ofNat_le.2 <| Nat.find_min' _ h) _⟩
#align int.least_of_bdd Int.leastOfBdd
-/

/- warning: int.exists_least_of_bdd -> Int.exists_least_of_bdd is a dubious translation:
lean 3 declaration is
  forall {P : Int -> Prop}, (Exists.{1} Int (fun (b : Int) => forall (z : Int), (P z) -> (LE.le.{0} Int Int.hasLe b z))) -> (Exists.{1} Int (fun (z : Int) => P z)) -> (Exists.{1} Int (fun (lb : Int) => And (P lb) (forall (z : Int), (P z) -> (LE.le.{0} Int Int.hasLe lb z))))
but is expected to have type
  forall {P : Int -> Prop} [Hbdd : DecidablePred.{1} Int P], (Exists.{1} Int (fun (z : Int) => forall (z_1 : Int), (P z_1) -> (LE.le.{0} Int Int.instLEInt z z_1))) -> (Exists.{1} Int (fun (z : Int) => P z)) -> (Exists.{1} Int (fun (lb : Int) => And (P lb) (forall (z : Int), (P z) -> (LE.le.{0} Int Int.instLEInt lb z))))
Case conversion may be inaccurate. Consider using '#align int.exists_least_of_bdd Int.exists_least_of_bddₓ'. -/
/-- If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded below and nonempty,
then this set has the least element. This lemma uses classical logic to avoid assumption
`[decidable_pred P]`. See `int.least_of_bdd` for a constructive counterpart. -/
theorem exists_least_of_bdd {P : ℤ → Prop} (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → b ≤ z)
    (Hinh : ∃ z : ℤ, P z) : ∃ lb : ℤ, P lb ∧ ∀ z : ℤ, P z → lb ≤ z := by
  classical exact
      let ⟨b, Hb⟩ := Hbdd
      let ⟨lb, H⟩ := least_of_bdd b Hb Hinh
      ⟨lb, H⟩
#align int.exists_least_of_bdd Int.exists_least_of_bdd

#print Int.coe_leastOfBdd_eq /-
theorem coe_leastOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → b ≤ z)
    (Hb' : ∀ z : ℤ, P z → b' ≤ z) (Hinh : ∃ z : ℤ, P z) :
    (leastOfBdd b Hb Hinh : ℤ) = leastOfBdd b' Hb' Hinh :=
  by
  rcases least_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases least_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n _ hn') (h2n' _ hn)
#align int.coe_least_of_bdd_eq Int.coe_leastOfBdd_eq
-/

#print Int.greatestOfBdd /-
/-- A computable version of `exists_greatest_of_bdd`: given a decidable predicate on the
integers, with an explicit upper bound and a proof that it is somewhere true, return
the greatest value for which the predicate is true. -/
def greatestOfBdd {P : ℤ → Prop} [DecidablePred P] (b : ℤ) (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : { ub : ℤ // P ub ∧ ∀ z : ℤ, P z → z ≤ ub } :=
  have Hbdd' : ∀ z : ℤ, P (-z) → -b ≤ z := fun z h => neg_le.1 (Hb _ h)
  have Hinh' : ∃ z : ℤ, P (-z) :=
    let ⟨elt, Helt⟩ := Hinh
    ⟨-elt, by rw [neg_neg] <;> exact Helt⟩
  let ⟨lb, Plb, al⟩ := leastOfBdd (-b) Hbdd' Hinh'
  ⟨-lb, Plb, fun z h => le_neg.1 <| al _ <| by rwa [neg_neg]⟩
#align int.greatest_of_bdd Int.greatestOfBdd
-/

/- warning: int.exists_greatest_of_bdd -> Int.exists_greatest_of_bdd is a dubious translation:
lean 3 declaration is
  forall {P : Int -> Prop}, (Exists.{1} Int (fun (b : Int) => forall (z : Int), (P z) -> (LE.le.{0} Int Int.hasLe z b))) -> (Exists.{1} Int (fun (z : Int) => P z)) -> (Exists.{1} Int (fun (ub : Int) => And (P ub) (forall (z : Int), (P z) -> (LE.le.{0} Int Int.hasLe z ub))))
but is expected to have type
  forall {P : Int -> Prop} [Hbdd : DecidablePred.{1} Int P], (Exists.{1} Int (fun (z : Int) => forall (z_1 : Int), (P z_1) -> (LE.le.{0} Int Int.instLEInt z_1 z))) -> (Exists.{1} Int (fun (z : Int) => P z)) -> (Exists.{1} Int (fun (ub : Int) => And (P ub) (forall (z : Int), (P z) -> (LE.le.{0} Int Int.instLEInt z ub))))
Case conversion may be inaccurate. Consider using '#align int.exists_greatest_of_bdd Int.exists_greatest_of_bddₓ'. -/
/-- If `P : ℤ → Prop` is a predicate such that the set `{m : P m}` is bounded above and nonempty,
then this set has the greatest element. This lemma uses classical logic to avoid assumption
`[decidable_pred P]`. See `int.greatest_of_bdd` for a constructive counterpart. -/
theorem exists_greatest_of_bdd {P : ℤ → Prop} (Hbdd : ∃ b : ℤ, ∀ z : ℤ, P z → z ≤ b)
    (Hinh : ∃ z : ℤ, P z) : ∃ ub : ℤ, P ub ∧ ∀ z : ℤ, P z → z ≤ ub := by
  classical exact
      let ⟨b, Hb⟩ := Hbdd
      let ⟨lb, H⟩ := greatest_of_bdd b Hb Hinh
      ⟨lb, H⟩
#align int.exists_greatest_of_bdd Int.exists_greatest_of_bdd

#print Int.coe_greatestOfBdd_eq /-
theorem coe_greatestOfBdd_eq {P : ℤ → Prop} [DecidablePred P] {b b' : ℤ} (Hb : ∀ z : ℤ, P z → z ≤ b)
    (Hb' : ∀ z : ℤ, P z → z ≤ b') (Hinh : ∃ z : ℤ, P z) :
    (greatestOfBdd b Hb Hinh : ℤ) = greatestOfBdd b' Hb' Hinh :=
  by
  rcases greatest_of_bdd b Hb Hinh with ⟨n, hn, h2n⟩
  rcases greatest_of_bdd b' Hb' Hinh with ⟨n', hn', h2n'⟩
  exact le_antisymm (h2n' _ hn) (h2n _ hn')
#align int.coe_greatest_of_bdd_eq Int.coe_greatestOfBdd_eq
-/

end Int

