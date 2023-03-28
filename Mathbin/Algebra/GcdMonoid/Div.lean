/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca

! This file was ported from Lean 3 source module algebra.gcd_monoid.div
! leanprover-community/mathlib commit b537794f8409bc9598febb79cd510b1df5f4539d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.GcdMonoid.Finset
import Mathbin.Algebra.GcdMonoid.Basic
import Mathbin.RingTheory.Int.Basic
import Mathbin.RingTheory.Polynomial.Content

/-!
# Basic results about setwise gcds on normalized gcd monoid with a division.

## Main results

* `finset.nat.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℕ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.int.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from `s` to
  `ℤ`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.
* `finset.polynomial.gcd_div_eq_one`: given a nonempty finset `s` and a function `f` from
  `s` to `K[X]`, if `d = s.gcd`, then the `gcd` of `(f i) / d` equals `1`.

## TODO
Add a typeclass to state these results uniformly.

-/


namespace Finset

namespace Nat

/- warning: finset.nat.gcd_div_eq_one -> Finset.Nat.gcd_div_eq_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> Nat} (s : Finset.{u1} β) {x : β}, (Membership.Mem.{u1, u1} β (Finset.{u1} β) (Finset.hasMem.{u1} β) x s) -> (Ne.{1} Nat (f x) (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Nat (Finset.gcd.{0, u1} Nat β Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid s (fun (b : β) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) (f b) (Finset.gcd.{0, u1} Nat β Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid s f))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {β : Type.{u1}} {f : β -> Nat} (s : Finset.{u1} β) {x : β}, (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s) -> (Ne.{1} Nat (f x) (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Nat (Finset.gcd.{0, u1} Nat β Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero s (fun (b : β) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) (f b) (Finset.gcd.{0, u1} Nat β Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero s f))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finset.nat.gcd_div_eq_one Finset.Nat.gcd_div_eq_oneₓ'. -/
/-- Given a nonempty finset `s` and a function `f` from `s` to `ℕ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → ℕ} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 :=
  by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, Nat.mul_div_cancel_left]
  exact Nat.pos_of_ne_zero (mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx)
#align finset.nat.gcd_div_eq_one Finset.Nat.gcd_div_eq_one

/- warning: finset.nat.gcd_div_id_eq_one -> Finset.Nat.gcd_div_id_eq_one is a dubious translation:
lean 3 declaration is
  forall {s : Finset.{0} Nat} {x : Nat}, (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) x s) -> (Ne.{1} Nat x (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) -> (Eq.{1} Nat (Finset.gcd.{0, 0} Nat Nat Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid s (fun (b : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.hasDiv) b (Finset.gcd.{0, 0} Nat Nat Nat.cancelCommMonoidWithZero Nat.normalizedGcdMonoid s (id.{1} Nat)))) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))
but is expected to have type
  forall {s : Finset.{0} Nat} {x : Nat}, (Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) x s) -> (Ne.{1} Nat x (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) -> (Eq.{1} Nat (Finset.gcd.{0, 0} Nat Nat Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero s (fun (b : Nat) => HDiv.hDiv.{0, 0, 0} Nat Nat Nat (instHDiv.{0} Nat Nat.instDivNat) b (Finset.gcd.{0, 0} Nat Nat Nat.cancelCommMonoidWithZero instNormalizedGCDMonoidNatCancelCommMonoidWithZero s (id.{1} Nat)))) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))
Case conversion may be inaccurate. Consider using '#align finset.nat.gcd_div_id_eq_one Finset.Nat.gcd_div_id_eq_oneₓ'. -/
theorem gcd_div_id_eq_one {s : Finset ℕ} {x : ℕ} (hx : x ∈ s) (hnz : x ≠ 0) :
    (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.nat.gcd_div_id_eq_one Finset.Nat.gcd_div_id_eq_one

end Nat

namespace Int

/- warning: finset.int.gcd_div_eq_one -> Finset.Int.gcd_div_eq_one is a dubious translation:
lean 3 declaration is
  forall {β : Type.{u1}} {f : β -> Int} (s : Finset.{u1} β) {x : β}, (Membership.Mem.{u1, u1} β (Finset.{u1} β) (Finset.hasMem.{u1} β) x s) -> (Ne.{1} Int (f x) (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Int (Finset.gcd.{0, u1} Int β (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizedGcdMonoid s (fun (b : β) => HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) (f b) (Finset.gcd.{0, u1} Int β (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizedGcdMonoid s f))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {β : Type.{u1}} {f : β -> Int} (s : Finset.{u1} β) {x : β}, (Membership.mem.{u1, u1} β (Finset.{u1} β) (Finset.instMembershipFinset.{u1} β) x s) -> (Ne.{1} Int (f x) (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} Int (Finset.gcd.{0, u1} Int β (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.instNormalizedGCDMonoidIntToCancelCommMonoidWithZeroInstCommSemiringIntIsDomainToLinearOrderedRingLinearOrderedCommRing s (fun (b : β) => HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) (f b) (Finset.gcd.{0, u1} Int β (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.instNormalizedGCDMonoidIntToCancelCommMonoidWithZeroInstCommSemiringIntIsDomainToLinearOrderedRingLinearOrderedCommRing s f))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align finset.int.gcd_div_eq_one Finset.Int.gcd_div_eq_oneₓ'. -/
/-- Given a nonempty finset `s` and a function `f` from `s` to `ℤ`, if `d = s.gcd`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → ℤ} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 :=
  by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, Int.mul_ediv_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx
#align finset.int.gcd_div_eq_one Finset.Int.gcd_div_eq_one

/- warning: finset.int.gcd_div_id_eq_one -> Finset.Int.gcd_div_id_eq_one is a dubious translation:
lean 3 declaration is
  forall {s : Finset.{0} Int} {x : Int}, (Membership.Mem.{0, 0} Int (Finset.{0} Int) (Finset.hasMem.{0} Int) x s) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (OfNat.mk.{0} Int 0 (Zero.zero.{0} Int Int.hasZero)))) -> (Eq.{1} Int (Finset.gcd.{0, 0} Int Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizedGcdMonoid s (fun (b : Int) => HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.hasDiv) b (Finset.gcd.{0, 0} Int Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.commSemiring (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.normalizedGcdMonoid s (id.{1} Int)))) (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne))))
but is expected to have type
  forall {s : Finset.{0} Int} {x : Int}, (Membership.mem.{0, 0} Int (Finset.{0} Int) (Finset.instMembershipFinset.{0} Int) x s) -> (Ne.{1} Int x (OfNat.ofNat.{0} Int 0 (instOfNatInt 0))) -> (Eq.{1} Int (Finset.gcd.{0, 0} Int Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.instNormalizedGCDMonoidIntToCancelCommMonoidWithZeroInstCommSemiringIntIsDomainToLinearOrderedRingLinearOrderedCommRing s (fun (b : Int) => HDiv.hDiv.{0, 0, 0} Int Int Int (instHDiv.{0} Int Int.instDivInt_1) b (Finset.gcd.{0, 0} Int Int (IsDomain.toCancelCommMonoidWithZero.{0} Int Int.instCommSemiringInt (LinearOrderedRing.isDomain.{0} Int (LinearOrderedCommRing.toLinearOrderedRing.{0} Int Int.linearOrderedCommRing))) Int.instNormalizedGCDMonoidIntToCancelCommMonoidWithZeroInstCommSemiringIntIsDomainToLinearOrderedRingLinearOrderedCommRing s (id.{1} Int)))) (OfNat.ofNat.{0} Int 1 (instOfNatInt 1)))
Case conversion may be inaccurate. Consider using '#align finset.int.gcd_div_id_eq_one Finset.Int.gcd_div_id_eq_oneₓ'. -/
theorem gcd_div_id_eq_one {s : Finset ℤ} {x : ℤ} (hx : x ∈ s) (hnz : x ≠ 0) :
    (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.int.gcd_div_id_eq_one Finset.Int.gcd_div_id_eq_one

end Int

namespace Polynomial

open Polynomial Classical

noncomputable section

variable {K : Type _} [Field K]

#print Finset.Polynomial.gcd_div_eq_one /-
/-- Given a nonempty finset `s` and a function `f` from `s` to `K[X]`, if `d = s.gcd f`,
then the `gcd` of `(f i) / d` is equal to `1`. -/
theorem gcd_div_eq_one {β : Type _} {f : β → K[X]} (s : Finset β) {x : β} (hx : x ∈ s)
    (hfz : f x ≠ 0) : (s.gcd fun b => f b / s.gcd f) = 1 :=
  by
  obtain ⟨g, he, hg⟩ := Finset.extract_gcd f ⟨x, hx⟩
  refine' (Finset.gcd_congr rfl fun a ha => _).trans hg
  rw [he a ha, EuclideanDomain.mul_div_cancel_left]
  exact mt Finset.gcd_eq_zero_iff.1 fun h => hfz <| h x hx
#align finset.polynomial.gcd_div_eq_one Finset.Polynomial.gcd_div_eq_one
-/

#print Finset.Polynomial.gcd_div_id_eq_one /-
theorem gcd_div_id_eq_one {s : Finset K[X]} {x : K[X]} (hx : x ∈ s) (hnz : x ≠ 0) :
    (s.gcd fun b => b / s.gcd id) = 1 :=
  gcd_div_eq_one s hx hnz
#align finset.polynomial.gcd_div_id_eq_one Finset.Polynomial.gcd_div_id_eq_one
-/

end Polynomial

end Finset

