/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Chris Hughes

! This file was ported from Lean 3 source module ring_theory.euclidean_domain
! leanprover-community/mathlib commit 70fd9563a21e7b963887c9360bd29b2393e6225a
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.Algebra.EuclideanDomain.Basic
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.PrincipalIdealDomain

/-!
# Lemmas about Euclidean domains

Various about Euclidean domains are proved; all of them seem to be true
more generally for principal ideal domains, so these lemmas should
probably be reproved in more generality and this file perhaps removed?

## Tags

euclidean domain
-/


noncomputable section

open Classical

open EuclideanDomain Set Ideal

section GCDMonoid

variable {R : Type _} [EuclideanDomain R] [GCDMonoid R]

/- warning: gcd_ne_zero_of_left -> gcd_ne_zero_of_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1))] (p : R) (q : R), (Ne.{succ u1} R p (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Ne.{succ u1} R (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1)) _inst_2 p q) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))] (p : R) (q : R), (Ne.{succ u1} R p (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) -> (Ne.{succ u1} R (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)) _inst_2 p q) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align gcd_ne_zero_of_left gcd_ne_zero_of_leftₓ'. -/
theorem gcd_ne_zero_of_left (p q : R) (hp : p ≠ 0) : GCDMonoid.gcd p q ≠ 0 := fun h =>
  hp <| eq_zero_of_zero_dvd (h ▸ gcd_dvd_left p q)
#align gcd_ne_zero_of_left gcd_ne_zero_of_left

/- warning: gcd_ne_zero_of_right -> gcd_ne_zero_of_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1))] (p : R) (q : R), (Ne.{succ u1} R q (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Ne.{succ u1} R (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1)) _inst_2 p q) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))] (p : R) (q : R), (Ne.{succ u1} R q (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) -> (Ne.{succ u1} R (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)) _inst_2 p q) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align gcd_ne_zero_of_right gcd_ne_zero_of_rightₓ'. -/
theorem gcd_ne_zero_of_right (p q : R) (hp : q ≠ 0) : GCDMonoid.gcd p q ≠ 0 := fun h =>
  hp <| eq_zero_of_zero_dvd (h ▸ gcd_dvd_right p q)
#align gcd_ne_zero_of_right gcd_ne_zero_of_right

/- warning: left_div_gcd_ne_zero -> left_div_gcd_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1))] {p : R} {q : R}, (Ne.{succ u1} R p (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Ne.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) p (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1)) _inst_2 p q)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))] {p : R} {q : R}, (Ne.{succ u1} R p (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) -> (Ne.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) p (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)) _inst_2 p q)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align left_div_gcd_ne_zero left_div_gcd_ne_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([1]) } -/
theorem left_div_gcd_ne_zero {p q : R} (hp : p ≠ 0) : p / GCDMonoid.gcd p q ≠ 0 :=
  by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_left p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hp)
  rw [hr, mul_comm, mul_div_cancel _ pq0]
  exact r0
#align left_div_gcd_ne_zero left_div_gcd_ne_zero

/- warning: right_div_gcd_ne_zero -> right_div_gcd_ne_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1))] {p : R} {q : R}, (Ne.{succ u1} R q (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1))))))))))) -> (Ne.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.hasDiv.{u1} R _inst_1)) q (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.isDomain.{u1} R _inst_1)) _inst_2 p q)) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : EuclideanDomain.{u1} R] [_inst_2 : GCDMonoid.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))] {p : R} {q : R}, (Ne.{succ u1} R q (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1))))))) -> (Ne.{succ u1} R (HDiv.hDiv.{u1, u1, u1} R R R (instHDiv.{u1} R (EuclideanDomain.instDiv.{u1} R _inst_1)) q (GCDMonoid.gcd.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)) _inst_2 p q)) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} R (IsDomain.toCancelCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R (EuclideanDomain.toCommRing.{u1} R _inst_1)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} R _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align right_div_gcd_ne_zero right_div_gcd_ne_zeroₓ'. -/
/- ./././Mathport/Syntax/Translate/Tactic/Lean3.lean:132:4: warning: unsupported: rw with cfg: { occs := occurrences.pos[occurrences.pos] «expr[ ,]»([1]) } -/
theorem right_div_gcd_ne_zero {p q : R} (hq : q ≠ 0) : q / GCDMonoid.gcd p q ≠ 0 :=
  by
  obtain ⟨r, hr⟩ := GCDMonoid.gcd_dvd_right p q
  obtain ⟨pq0, r0⟩ : GCDMonoid.gcd p q ≠ 0 ∧ r ≠ 0 := mul_ne_zero_iff.mp (hr ▸ hq)
  rw [hr, mul_comm, mul_div_cancel _ pq0]
  exact r0
#align right_div_gcd_ne_zero right_div_gcd_ne_zero

end GCDMonoid

namespace EuclideanDomain

#print EuclideanDomain.gcdMonoid /-
/-- Create a `gcd_monoid` whose `gcd_monoid.gcd` matches `euclidean_domain.gcd`. -/
def gcdMonoid (R) [EuclideanDomain R] : GCDMonoid R
    where
  gcd := gcd
  lcm := lcm
  gcd_dvd_left := gcd_dvd_left
  gcd_dvd_right := gcd_dvd_right
  dvd_gcd a b c := dvd_gcd
  gcd_mul_lcm a b := by rw [EuclideanDomain.gcd_mul_lcm]
  lcm_zero_left := lcm_zero_left
  lcm_zero_right := lcm_zero_right
#align euclidean_domain.gcd_monoid EuclideanDomain.gcdMonoid
-/

variable {α : Type _} [EuclideanDomain α] [DecidableEq α]

#print EuclideanDomain.span_gcd /-
theorem span_gcd {α} [EuclideanDomain α] (x y : α) :
    span ({gcd x y} : Set α) = span ({x, y} : Set α) :=
  letI := EuclideanDomain.gcdMonoid α
  span_gcd x y
#align euclidean_domain.span_gcd EuclideanDomain.span_gcd
-/

/- warning: euclidean_domain.gcd_is_unit_iff -> EuclideanDomain.gcd_isUnit_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] {x : α} {y : α}, Iff (IsUnit.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))) (EuclideanDomain.gcd.{u1} α _inst_3 (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b)) x y)) (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] {x : α} {y : α}, Iff (IsUnit.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))) (EuclideanDomain.gcd.{u1} α _inst_3 (fun (a : α) (b : α) => Classical.propDecidable (Eq.{succ u1} α a b)) x y)) (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.gcd_is_unit_iff EuclideanDomain.gcd_isUnit_iffₓ'. -/
theorem gcd_isUnit_iff {α} [EuclideanDomain α] {x y : α} : IsUnit (gcd x y) ↔ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  gcd_isUnit_iff x y
#align euclidean_domain.gcd_is_unit_iff EuclideanDomain.gcd_isUnit_iff

/- warning: euclidean_domain.is_coprime_of_dvd -> EuclideanDomain.isCoprime_of_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] {x : α} {y : α}, (Not (And (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))))))) (Eq.{succ u1} α y (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))))))))) -> (forall (z : α), (Membership.Mem.{u1, u1} α (Set.{u1} α) (Set.hasMem.{u1} α) z (nonunits.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))) -> (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))))))) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) z x) -> (Not (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) z y))) -> (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y)
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] {x : α} {y : α}, (Not (And (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} α _inst_3))))))) (Eq.{succ u1} α y (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} α _inst_3))))))))) -> (forall (z : α), (Membership.mem.{u1, u1} α (Set.{u1} α) (Set.instMembershipSet.{u1} α) z (nonunits.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) -> (Ne.{succ u1} α z (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α (IsDomain.toCancelCommMonoidWithZero.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) (EuclideanDomain.instIsDomainToSemiringToRingToCommRing.{u1} α _inst_3))))))) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) z x) -> (Not (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) z y))) -> (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y)
Case conversion may be inaccurate. Consider using '#align euclidean_domain.is_coprime_of_dvd EuclideanDomain.isCoprime_of_dvdₓ'. -/
-- this should be proved for UFDs surely?
theorem isCoprime_of_dvd {α} [EuclideanDomain α] {x y : α} (nonzero : ¬(x = 0 ∧ y = 0))
    (H : ∀ z ∈ nonunits α, z ≠ 0 → z ∣ x → ¬z ∣ y) : IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  isCoprime_of_dvd x y nonzero H
#align euclidean_domain.is_coprime_of_dvd EuclideanDomain.isCoprime_of_dvd

/- warning: euclidean_domain.dvd_or_coprime -> EuclideanDomain.dvd_or_coprime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] (x : α) (y : α), (Irreducible.{u1} α (Ring.toMonoid.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))) x) -> (Or (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) x y) (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y))
but is expected to have type
  forall {α : Type.{u1}} [_inst_3 : EuclideanDomain.{u1} α] (x : α) (y : α), (Irreducible.{u1} α (MonoidWithZero.toMonoid.{u1} α (Semiring.toMonoidWithZero.{u1} α (Ring.toSemiring.{u1} α (CommRing.toRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))) x) -> (Or (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α (CommRing.toNonUnitalCommRing.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3))))))) x y) (IsCoprime.{u1} α (CommRing.toCommSemiring.{u1} α (EuclideanDomain.toCommRing.{u1} α _inst_3)) x y))
Case conversion may be inaccurate. Consider using '#align euclidean_domain.dvd_or_coprime EuclideanDomain.dvd_or_coprimeₓ'. -/
-- this should be proved for UFDs surely?
theorem dvd_or_coprime {α} [EuclideanDomain α] (x y : α) (h : Irreducible x) :
    x ∣ y ∨ IsCoprime x y :=
  letI := EuclideanDomain.gcdMonoid α
  dvd_or_coprime x y h
#align euclidean_domain.dvd_or_coprime EuclideanDomain.dvd_or_coprime

end EuclideanDomain

