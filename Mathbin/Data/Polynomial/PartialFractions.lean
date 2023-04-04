/-
Copyright (c) Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan

! This file was ported from Lean 3 source module data.polynomial.partial_fractions
! leanprover-community/mathlib commit 31ca6f9cf5f90a6206092cd7f84b359dcb6d52e0
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Div
import Mathbin.Data.Zmod.Basic
import Mathbin.Logic.Function.Basic
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.Tactic.FieldSimp
import Mathbin.Tactic.LinearCombination

/-!

# Partial fractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


# The main theorem

* `div_eq_quo_add_sum_rem_div`: General partial fraction decomposition theorem for polynomials over
  an integral domain R :
  If f, g₁, g₂, ..., gₙ ∈ R[X] and the gᵢs are all monic and pairwise coprime, then ∃ q, r₁, ..., rₙ
  ∈ R[X] such that f / g₁g₂...gₙ = q + r₁/g₁ + ... + rₙ/gₙ and for all i, deg(rᵢ) < deg(gᵢ).

* The result is formalized here in slightly more generality, using finsets. That is, if ι is an
  arbitrary index type, g denotes a map from ι to R[X], and if s is an arbitrary finite subset of ι,
  with g i monic for all i ∈ s and for all i,j ∈ s, i ≠ j → g i is coprime to g j, then we have
  ∃ q ∈ R[X] , r : ι → R[X] such that ∀ i ∈ s, deg(r i) < deg(g i) and
  f / ∏ g i = q + ∑ (r i) / (g i), where the product and sum are over s.

* The proof is done by proving the two-denominator case and then performing finset induction for an
  arbitrary (finite) number of denominators.

## Scope for Expansion

* Proving uniqueness of the decomposition

-/


variable (R : Type) [CommRing R] [IsDomain R]

open Polynomial

open Polynomial

variable (K : Type) [Field K] [Algebra R[X] K] [IsFractionRing R[X] K]

section TwoDenominators

/- warning: div_eq_quo_add_rem_div_add_rem_div -> div_eq_quo_add_rem_div_add_rem_div is a dubious translation:
lean 3 declaration is
  forall (R : Type) [_inst_1 : CommRing.{0} R] [_inst_2 : IsDomain.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))] (K : Type) [_inst_3 : Field.{0} K] [_inst_4 : Algebra.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))] [_inst_5 : IsFractionRing.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commRing.{0} R _inst_1) K (Field.toCommRing.{0} K _inst_3) _inst_4] (f : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) {g₁ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))} {g₂ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))}, (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₁) -> (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₂) -> (IsCoprime.{0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) g₁ g₂) -> (Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (q : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (r₁ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (r₂ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => And (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) r₁) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₁)) (And (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) r₂) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₂)) (Eq.{1} K (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (DivInvMonoid.toHasDiv.{0} K (DivisionRing.toDivInvMonoid.{0} K (Field.toDivisionRing.{0} K _inst_3)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) f) (HMul.hMul.{0, 0, 0} K K K (instHMul.{0} K (Distrib.toHasMul.{0} K (Ring.toDistrib.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) g₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) g₂))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toHasAdd.{0} K (Ring.toDistrib.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toHasAdd.{0} K (Ring.toDistrib.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) q) (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (DivInvMonoid.toHasDiv.{0} K (DivisionRing.toDivInvMonoid.{0} K (Field.toDivisionRing.{0} K _inst_3)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) r₁) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) g₁))) (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (DivInvMonoid.toHasDiv.{0} K (DivisionRing.toDivInvMonoid.{0} K (Field.toDivisionRing.{0} K _inst_3)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) r₂) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) g₂)))))))))
but is expected to have type
  forall (R : Type) [_inst_1 : CommRing.{0} R] [_inst_2 : IsDomain.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))] (K : Type) [_inst_3 : Field.{0} K] [_inst_4 : Algebra.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3)))] [_inst_5 : IsFractionRing.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commRing.{0} R _inst_1) K (Field.toCommRing.{0} K _inst_3) _inst_4] (f : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) {g₁ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))} {g₂ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))}, (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₁) -> (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₂) -> (IsCoprime.{0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) g₁ g₂) -> (Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (q : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (r₁ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (r₂ : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => And (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) r₁) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₁)) (And (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) r₂) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) g₂)) (Eq.{1} K (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (Field.toDiv.{0} K _inst_3)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 f) (HMul.hMul.{0, 0, 0} K K K (instHMul.{0} K (NonUnitalNonAssocRing.toMul.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 g₁) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 g₂))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toAdd.{0} K (NonUnitalNonAssocSemiring.toDistrib.{0} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toAdd.{0} K (NonUnitalNonAssocSemiring.toDistrib.{0} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))))) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 q) (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (Field.toDiv.{0} K _inst_3)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 r₁) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 g₁))) (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (Field.toDiv.{0} K _inst_3)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 r₂) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 g₂)))))))))
Case conversion may be inaccurate. Consider using '#align div_eq_quo_add_rem_div_add_rem_div div_eq_quo_add_rem_div_add_rem_divₓ'. -/
/-- Let R be an integral domain and f, g₁, g₂ ∈ R[X]. Let g₁ and g₂ be monic and coprime.
Then, ∃ q, r₁, r₂ ∈ R[X] such that f / g₁g₂ = q + r₁/g₁ + r₂/g₂ and deg(r₁) < deg(g₁) and
deg(r₂) < deg(g₂).
-/
theorem div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) :
    ∃ q r₁ r₂ : R[X],
      r₁.degree < g₁.degree ∧
        r₂.degree < g₂.degree ∧ (↑f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ :=
  by
  rcases hcoprime with ⟨c, d, hcd⟩
  refine'
    ⟨f * d /ₘ g₁ + f * c /ₘ g₂, f * d %ₘ g₁, f * c %ₘ g₂, degree_mod_by_monic_lt _ hg₁,
      degree_mod_by_monic_lt _ hg₂, _⟩
  have hg₁' : (↑g₁ : K) ≠ 0 := by
    norm_cast
    exact hg₁.ne_zero_of_ne zero_ne_one
  have hg₂' : (↑g₂ : K) ≠ 0 := by
    norm_cast
    exact hg₂.ne_zero_of_ne zero_ne_one
  have hfc := mod_by_monic_add_div (f * c) hg₂
  have hfd := mod_by_monic_add_div (f * d) hg₁
  field_simp
  norm_cast
  linear_combination -1 * f * hcd + -1 * g₁ * hfc + -1 * g₂ * hfd
#align div_eq_quo_add_rem_div_add_rem_div div_eq_quo_add_rem_div_add_rem_div

end TwoDenominators

section NDenominators

open BigOperators Classical

/- warning: div_eq_quo_add_sum_rem_div -> div_eq_quo_add_sum_rem_div is a dubious translation:
lean 3 declaration is
  forall (R : Type) [_inst_1 : CommRing.{0} R] [_inst_2 : IsDomain.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))] (K : Type) [_inst_3 : Field.{0} K] [_inst_4 : Algebra.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))] [_inst_5 : IsFractionRing.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commRing.{0} R _inst_1) K (Field.toCommRing.{0} K _inst_3) _inst_4] (f : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) {ι : Type.{u1}} {g : ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (g i))) -> (Set.Pairwise.{u1} ι ((fun (a : Type.{u1}) (b : Type.{u1}) [self : HasLiftT.{succ u1, succ u1} a b] => self.0) (Finset.{u1} ι) (Set.{u1} ι) (HasLiftT.mk.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (CoeTCₓ.coe.{succ u1, succ u1} (Finset.{u1} ι) (Set.{u1} ι) (Finset.Set.hasCoeT.{u1} ι))) s) (fun (i : ι) (j : ι) => IsCoprime.{0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (g i) (g j))) -> (Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (q : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{succ u1} (ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))) (fun (r : ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))) => And (forall (i : ι), (Membership.Mem.{u1, u1} ι (Finset.{u1} ι) (Finset.hasMem.{u1} ι) i s) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (OrderedCancelAddCommMonoid.toPartialOrder.{0} Nat (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} Nat Nat.strictOrderedSemiring))))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (r i)) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (g i)))) (Eq.{1} K (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (DivInvMonoid.toHasDiv.{0} K (DivisionRing.toDivInvMonoid.{0} K (Field.toDivisionRing.{0} K _inst_3)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) f) (Finset.prod.{0, u1} K ι (CommRing.toCommMonoid.{0} K (Field.toCommRing.{0} K _inst_3)) s (fun (i : ι) => (fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) (g i)))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toHasAdd.{0} K (Ring.toDistrib.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) q) (Finset.sum.{0, u1} K ι (AddCommGroup.toAddCommMonoid.{0} K (NonUnitalNonAssocRing.toAddCommGroup.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))) s (fun (i : ι) => HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (DivInvMonoid.toHasDiv.{0} K (DivisionRing.toDivInvMonoid.{0} K (Field.toDivisionRing.{0} K _inst_3)))) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) (r i)) ((fun (a : Type) (b : Type) [self : HasLiftT.{1, 1} a b] => self.0) (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (algebraMap.coeHTCT.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (Ring.toSemiring.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3))) _inst_4) (g i)))))))))
but is expected to have type
  forall (R : Type) [_inst_1 : CommRing.{0} R] [_inst_2 : IsDomain.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))] (K : Type) [_inst_3 : Field.{0} K] [_inst_4 : Algebra.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3)))] [_inst_5 : IsFractionRing.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commRing.{0} R _inst_1) K (Field.toCommRing.{0} K _inst_3) _inst_4] (f : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) {ι : Type.{u1}} {g : ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))} {s : Finset.{u1} ι}, (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (Polynomial.Monic.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (g i))) -> (Set.Pairwise.{u1} ι (Finset.toSet.{u1} ι s) (fun (i : ι) (j : ι) => IsCoprime.{0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (g i) (g j))) -> (Exists.{1} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) (fun (q : Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) => Exists.{succ u1} (ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))) (fun (r : ι -> (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)))) => And (forall (i : ι), (Membership.mem.{u1, u1} ι (Finset.{u1} ι) (Finset.instMembershipFinset.{u1} ι) i s) -> (LT.lt.{0} (WithBot.{0} Nat) (Preorder.toLT.{0} (WithBot.{0} Nat) (WithBot.preorder.{0} Nat (PartialOrder.toPreorder.{0} Nat (StrictOrderedSemiring.toPartialOrder.{0} Nat Nat.strictOrderedSemiring)))) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (r i)) (Polynomial.degree.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1)) (g i)))) (Eq.{1} K (HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (Field.toDiv.{0} K _inst_3)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 f) (Finset.prod.{0, u1} K ι (CommRing.toCommMonoid.{0} K (Field.toCommRing.{0} K _inst_3)) s (fun (i : ι) => Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 (g i)))) (HAdd.hAdd.{0, 0, 0} K K K (instHAdd.{0} K (Distrib.toAdd.{0} K (NonUnitalNonAssocSemiring.toDistrib.{0} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))))) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 q) (Finset.sum.{0, u1} K ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{0} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{0} K (NonAssocRing.toNonUnitalNonAssocRing.{0} K (Ring.toNonAssocRing.{0} K (DivisionRing.toRing.{0} K (Field.toDivisionRing.{0} K _inst_3)))))) s (fun (i : ι) => HDiv.hDiv.{0, 0, 0} K K K (instHDiv.{0} K (Field.toDiv.{0} K _inst_3)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 (r i)) (Algebra.cast.{0, 0} (Polynomial.{0} R (Ring.toSemiring.{0} R (CommRing.toRing.{0} R _inst_1))) K (Polynomial.commSemiring.{0} R (CommRing.toCommSemiring.{0} R _inst_1)) (DivisionSemiring.toSemiring.{0} K (Semifield.toDivisionSemiring.{0} K (Field.toSemifield.{0} K _inst_3))) _inst_4 (g i)))))))))
Case conversion may be inaccurate. Consider using '#align div_eq_quo_add_sum_rem_div div_eq_quo_add_sum_rem_divₓ'. -/
/-- Let R be an integral domain and f ∈ R[X]. Let s be a finite index set.
Then, a fraction of the form f / ∏ (g i) can be rewritten as q + ∑ (r i) / (g i), where
deg(r i) < deg(g i), provided that the g i are monic and pairwise coprime.
-/
theorem div_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type _} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X])(r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i in s, ↑(g i)) = ↑q + ∑ i in s, ↑(r i) / ↑(g i) :=
  by
  induction' s using Finset.induction_on with a b hab Hind f generalizing f
  · refine' ⟨f, fun i : ι => (0 : R[X]), fun i => _, by simp⟩
    rintro ⟨⟩
  obtain ⟨q₀, r₁, r₂, hdeg₁, hdeg₂, hf : (↑f : K) / _ = _⟩ :=
    div_eq_quo_add_rem_div_add_rem_div R K f (_ : monic (g a)) (_ : monic (∏ i : ι in b, g i)) _
  · obtain ⟨q, r, hrdeg, IH⟩ :=
      Hind (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (Set.Pairwise.mono (Finset.coe_subset.2 fun i hi => Finset.mem_insert_of_mem hi) hcop) r₂
    refine' ⟨q₀ + q, fun i => if i = a then r₁ else r i, _, _⟩
    · intro i
      split_ifs with h1
      · cases h1
        intro
        exact hdeg₁
      · intro hi
        exact hrdeg i (Finset.mem_of_mem_insert_of_ne hi h1)
    norm_cast  at hf IH⊢
    rw [Finset.prod_insert hab, hf, IH, Finset.sum_insert hab, if_pos rfl]
    trans (↑(q₀ + q : R[X]) : K) + (↑r₁ / ↑(g a) + ∑ i : ι in b, ↑(r i) / ↑(g i))
    · push_cast
      ring
    congr 2
    refine' Finset.sum_congr rfl fun x hxb => _
    rw [if_neg]
    rintro rfl
    exact hab hxb
  · exact hg a (b.mem_insert_self a)
  · exact monic_prod_of_monic _ _ fun i hi => hg i (Finset.mem_insert_of_mem hi)
  · refine'
      IsCoprime.prod_right fun i hi =>
        hcop (Finset.mem_coe.2 (b.mem_insert_self a))
          (Finset.mem_coe.2 (Finset.mem_insert_of_mem hi)) _
    rintro rfl
    exact hab hi
#align div_eq_quo_add_sum_rem_div div_eq_quo_add_sum_rem_div

end NDenominators

