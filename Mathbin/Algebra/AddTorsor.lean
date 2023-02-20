/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov

! This file was ported from Lean 3 source module algebra.add_torsor
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Set.Pointwise.Smul

/-!
# Torsors of additive group actions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines torsors of additive group actions.

## Notations

The group elements are referred to as acting on points.  This file
defines the notation `+ᵥ` for adding a group element to a point and
`-ᵥ` for subtracting two points to produce a group element.

## Implementation notes

Affine spaces are the motivating example of torsors of additive group actions. It may be appropriate
to refactor in terms of the general definition of group actions, via `to_additive`, when there is a
use for multiplicative torsors (currently mathlib only develops the theory of group actions for
multiplicative group actions).

## Notations

* `v +ᵥ p` is a notation for `has_vadd.vadd`, the left action of an additive monoid;

* `p₁ -ᵥ p₂` is a notation for `has_vsub.vsub`, difference between two points in an additive torsor
  as an element of the corresponding additive group;

## References

* https://en.wikipedia.org/wiki/Principal_homogeneous_space
* https://en.wikipedia.org/wiki/Affine_space

-/


#print AddTorsor /-
/-- An `add_torsor G P` gives a structure to the nonempty type `P`,
acted on by an `add_group G` with a transitive and free action given
by the `+ᵥ` operation and a corresponding subtraction given by the
`-ᵥ` operation. In the case of a vector space, it is an affine
space. -/
class AddTorsor (G : outParam (Type _)) (P : Type _) [outParam <| AddGroup G] extends AddAction G P,
  VSub G P where
  [Nonempty : Nonempty P]
  vsub_vadd' : ∀ p1 p2 : P, (p1 -ᵥ p2 : G) +ᵥ p2 = p1
  vadd_vsub' : ∀ (g : G) (p : P), g +ᵥ p -ᵥ p = g
#align add_torsor AddTorsor
-/

attribute [instance, nolint dangerous_instance] AddTorsor.nonempty

attribute [nolint dangerous_instance] AddTorsor.toHasVsub

#print addGroupIsAddTorsor /-
/-- An `add_group G` is a torsor for itself. -/
@[nolint instance_priority]
instance addGroupIsAddTorsor (G : Type _) [AddGroup G] : AddTorsor G G
    where
  vsub := Sub.sub
  vsub_vadd' := sub_add_cancel
  vadd_vsub' := add_sub_cancel
#align add_group_is_add_torsor addGroupIsAddTorsor
-/

/- warning: vsub_eq_sub -> vsub_eq_sub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_1 : AddGroup.{u1} G] (g1 : G) (g2 : G), Eq.{succ u1} G (VSub.vsub.{u1, u1} G G (AddTorsor.toHasVsub.{u1, u1} G G _inst_1 (addGroupIsAddTorsor.{u1} G _inst_1)) g1 g2) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) g1 g2)
but is expected to have type
  forall {G : Type.{u1}} [_inst_1 : AddGroup.{u1} G] (g1 : G) (g2 : G), Eq.{succ u1} G (VSub.vsub.{u1, u1} G G (AddTorsor.toVSub.{u1, u1} G G _inst_1 (addGroupIsAddTorsor.{u1} G _inst_1)) g1 g2) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) g1 g2)
Case conversion may be inaccurate. Consider using '#align vsub_eq_sub vsub_eq_subₓ'. -/
/-- Simplify subtraction for a torsor for an `add_group G` over
itself. -/
@[simp]
theorem vsub_eq_sub {G : Type _} [AddGroup G] (g1 g2 : G) : g1 -ᵥ g2 = g1 - g2 :=
  rfl
#align vsub_eq_sub vsub_eq_sub

section General

variable {G : Type _} {P : Type _} [AddGroup G] [T : AddTorsor G P]

include T

#print vsub_vadd /-
/-- Adding the result of subtracting from another point produces that
point. -/
@[simp]
theorem vsub_vadd (p1 p2 : P) : p1 -ᵥ p2 +ᵥ p2 = p1 :=
  AddTorsor.vsub_vadd' p1 p2
#align vsub_vadd vsub_vadd
-/

/- warning: vadd_vsub -> vadd_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (g : G) (p : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) g p) p) g
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (g : G) (p : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) g p) p) g
Case conversion may be inaccurate. Consider using '#align vadd_vsub vadd_vsubₓ'. -/
/-- Adding a group element then subtracting the original point
produces that group element. -/
@[simp]
theorem vadd_vsub (g : G) (p : P) : g +ᵥ p -ᵥ p = g :=
  AddTorsor.vadd_vsub' g p
#align vadd_vsub vadd_vsub

#print vadd_right_cancel /-
/-- If the same point added to two group elements produces equal
results, those group elements are equal. -/
theorem vadd_right_cancel {g1 g2 : G} (p : P) (h : g1 +ᵥ p = g2 +ᵥ p) : g1 = g2 := by
  rw [← vadd_vsub g1, h, vadd_vsub]
#align vadd_right_cancel vadd_right_cancel
-/

#print vadd_right_cancel_iff /-
@[simp]
theorem vadd_right_cancel_iff {g1 g2 : G} (p : P) : g1 +ᵥ p = g2 +ᵥ p ↔ g1 = g2 :=
  ⟨vadd_right_cancel p, fun h => h ▸ rfl⟩
#align vadd_right_cancel_iff vadd_right_cancel_iff
-/

/- warning: vadd_right_injective -> vadd_right_injective is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p : P), Function.Injective.{succ u1, succ u2} G P (fun (_x : G) => VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) _x p)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p : P), Function.Injective.{succ u2, succ u1} G P (fun (_x : G) => HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) _x p)
Case conversion may be inaccurate. Consider using '#align vadd_right_injective vadd_right_injectiveₓ'. -/
/-- Adding a group element to the point `p` is an injective
function. -/
theorem vadd_right_injective (p : P) : Function.Injective ((· +ᵥ p) : G → P) := fun g1 g2 =>
  vadd_right_cancel p
#align vadd_right_injective vadd_right_injective

/- warning: vadd_vsub_assoc -> vadd_vsub_assoc is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (g : G) (p1 : P) (p2 : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) g p1) p2) (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) g (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (g : G) (p1 : P) (p2 : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) g p1) p2) (HAdd.hAdd.{u2, u2, u2} G G G (instHAdd.{u2} G (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) g (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2))
Case conversion may be inaccurate. Consider using '#align vadd_vsub_assoc vadd_vsub_assocₓ'. -/
/-- Adding a group element to a point, then subtracting another point,
produces the same result as subtracting the points then adding the
group element. -/
theorem vadd_vsub_assoc (g : G) (p1 p2 : P) : g +ᵥ p1 -ᵥ p2 = g + (p1 -ᵥ p2) :=
  by
  apply vadd_right_cancel p2
  rw [vsub_vadd, add_vadd, vsub_vadd]
#align vadd_vsub_assoc vadd_vsub_assoc

/- warning: vsub_self -> vsub_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p p) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p p) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))))
Case conversion may be inaccurate. Consider using '#align vsub_self vsub_selfₓ'. -/
/-- Subtracting a point from itself produces 0. -/
@[simp]
theorem vsub_self (p : P) : p -ᵥ p = (0 : G) := by
  rw [← zero_add (p -ᵥ p), ← vadd_vsub_assoc, vadd_vsub]
#align vsub_self vsub_self

/- warning: eq_of_vsub_eq_zero -> eq_of_vsub_eq_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P}, (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))))) -> (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P}, (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))))) -> (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align eq_of_vsub_eq_zero eq_of_vsub_eq_zeroₓ'. -/
/-- If subtracting two points produces 0, they are equal. -/
theorem eq_of_vsub_eq_zero {p1 p2 : P} (h : p1 -ᵥ p2 = (0 : G)) : p1 = p2 := by
  rw [← vsub_vadd p1 p2, h, zero_vadd]
#align eq_of_vsub_eq_zero eq_of_vsub_eq_zero

/- warning: vsub_eq_zero_iff_eq -> vsub_eq_zero_iff_eq is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P}, Iff (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))))) (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P}, Iff (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))))) (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_eq_zero_iff_eq vsub_eq_zero_iff_eqₓ'. -/
/-- Subtracting two points produces 0 if and only if they are
equal. -/
@[simp]
theorem vsub_eq_zero_iff_eq {p1 p2 : P} : p1 -ᵥ p2 = (0 : G) ↔ p1 = p2 :=
  Iff.intro eq_of_vsub_eq_zero fun h => h ▸ vsub_self _
#align vsub_eq_zero_iff_eq vsub_eq_zero_iff_eq

/- warning: vsub_ne_zero -> vsub_ne_zero is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p : P} {q : P}, Iff (Ne.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p q) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))))) (Ne.{succ u2} P p q)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p : P} {q : P}, Iff (Ne.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p q) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1))))))) (Ne.{succ u1} P p q)
Case conversion may be inaccurate. Consider using '#align vsub_ne_zero vsub_ne_zeroₓ'. -/
theorem vsub_ne_zero {p q : P} : p -ᵥ q ≠ (0 : G) ↔ p ≠ q :=
  not_congr vsub_eq_zero_iff_eq
#align vsub_ne_zero vsub_ne_zero

/- warning: vsub_add_vsub_cancel -> vsub_add_vsub_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u1} G (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p2 p3)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p3)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u2} G (HAdd.hAdd.{u2, u2, u2} G G G (instHAdd.{u2} G (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p2 p3)) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p3)
Case conversion may be inaccurate. Consider using '#align vsub_add_vsub_cancel vsub_add_vsub_cancelₓ'. -/
/-- Cancellation adding the results of two subtractions. -/
@[simp]
theorem vsub_add_vsub_cancel (p1 p2 p3 : P) : p1 -ᵥ p2 + (p2 -ᵥ p3) = p1 -ᵥ p3 :=
  by
  apply vadd_right_cancel p3
  rw [add_vadd, vsub_vadd, vsub_vadd, vsub_vadd]
#align vsub_add_vsub_cancel vsub_add_vsub_cancel

/- warning: neg_vsub_eq_vsub_rev -> neg_vsub_eq_vsub_rev is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p1 : P) (p2 : P), Eq.{succ u1} G (Neg.neg.{u1} G (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p2 p1)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p1 : P) (p2 : P), Eq.{succ u2} G (Neg.neg.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2)) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p2 p1)
Case conversion may be inaccurate. Consider using '#align neg_vsub_eq_vsub_rev neg_vsub_eq_vsub_revₓ'. -/
/-- Subtracting two points in the reverse order produces the negation
of subtracting them. -/
@[simp]
theorem neg_vsub_eq_vsub_rev (p1 p2 : P) : -(p1 -ᵥ p2) = p2 -ᵥ p1 :=
  by
  refine' neg_eq_of_add_eq_zero_right (vadd_right_cancel p1 _)
  rw [vsub_add_vsub_cancel, vsub_self]
#align neg_vsub_eq_vsub_rev neg_vsub_eq_vsub_rev

/- warning: vadd_vsub_eq_sub_vsub -> vadd_vsub_eq_sub_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (g : G) (p : P) (q : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) g p) q) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) g (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) q p))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (g : G) (p : P) (q : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) g p) q) (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))) g (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) q p))
Case conversion may be inaccurate. Consider using '#align vadd_vsub_eq_sub_vsub vadd_vsub_eq_sub_vsubₓ'. -/
theorem vadd_vsub_eq_sub_vsub (g : G) (p q : P) : g +ᵥ p -ᵥ q = g - (q -ᵥ p) := by
  rw [vadd_vsub_assoc, sub_eq_add_neg, neg_vsub_eq_vsub_rev]
#align vadd_vsub_eq_sub_vsub vadd_vsub_eq_sub_vsub

/- warning: vsub_vadd_eq_vsub_sub -> vsub_vadd_eq_vsub_sub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p1 : P) (p2 : P) (g : G), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) g p2)) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2) g)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p1 : P) (p2 : P) (g : G), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) g p2)) (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2) g)
Case conversion may be inaccurate. Consider using '#align vsub_vadd_eq_vsub_sub vsub_vadd_eq_vsub_subₓ'. -/
/-- Subtracting the result of adding a group element produces the same result
as subtracting the points and subtracting that group element. -/
theorem vsub_vadd_eq_vsub_sub (p1 p2 : P) (g : G) : p1 -ᵥ (g +ᵥ p2) = p1 -ᵥ p2 - g := by
  rw [← add_right_inj (p2 -ᵥ p1 : G), vsub_add_vsub_cancel, ← neg_vsub_eq_vsub_rev, vadd_vsub, ←
    add_sub_assoc, ← neg_vsub_eq_vsub_rev, neg_add_self, zero_sub]
#align vsub_vadd_eq_vsub_sub vsub_vadd_eq_vsub_sub

/- warning: vsub_sub_vsub_cancel_right -> vsub_sub_vsub_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p3) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p2 p3)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u2} G (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p3) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p2 p3)) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_sub_vsub_cancel_right vsub_sub_vsub_cancel_rightₓ'. -/
/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_right (p1 p2 p3 : P) : p1 -ᵥ p3 - (p2 -ᵥ p3) = p1 -ᵥ p2 := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd]
#align vsub_sub_vsub_cancel_right vsub_sub_vsub_cancel_right

#print eq_vadd_iff_vsub_eq /-
/-- Convert between an equality with adding a group element to a point
and an equality of a subtraction of two points with a group
element. -/
theorem eq_vadd_iff_vsub_eq (p1 : P) (g : G) (p2 : P) : p1 = g +ᵥ p2 ↔ p1 -ᵥ p2 = g :=
  ⟨fun h => h.symm ▸ vadd_vsub _ _, fun h => h ▸ (vsub_vadd _ _).symm⟩
#align eq_vadd_iff_vsub_eq eq_vadd_iff_vsub_eq
-/

/- warning: vadd_eq_vadd_iff_neg_add_eq_vsub -> vadd_eq_vadd_iff_neg_add_eq_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P}, Iff (Eq.{succ u2} P (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) v₁ p₁) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) v₂ p₂)) (Eq.{succ u1} G (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) (Neg.neg.{u1} G (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) v₁) v₂) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p₁ p₂))
but is expected to have type
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P}, Iff (Eq.{succ u2} P (HVAdd.hVAdd.{u1, u2, u2} G P P (instHVAdd.{u1, u2} G P (AddAction.toVAdd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T))) v₁ p₁) (HVAdd.hVAdd.{u1, u2, u2} G P P (instHVAdd.{u1, u2} G P (AddAction.toVAdd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T))) v₂ p₂)) (Eq.{succ u1} G (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) (Neg.neg.{u1} G (NegZeroClass.toNeg.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_1)))) v₁) v₂) (VSub.vsub.{u1, u2} G P (AddTorsor.toVSub.{u1, u2} G P _inst_1 T) p₁ p₂))
Case conversion may be inaccurate. Consider using '#align vadd_eq_vadd_iff_neg_add_eq_vsub vadd_eq_vadd_iff_neg_add_eq_vsubₓ'. -/
theorem vadd_eq_vadd_iff_neg_add_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ -v₁ + v₂ = p₁ -ᵥ p₂ := by
  rw [eq_vadd_iff_vsub_eq, vadd_vsub_assoc, ← add_right_inj (-v₁), neg_add_cancel_left, eq_comm]
#align vadd_eq_vadd_iff_neg_add_eq_vsub vadd_eq_vadd_iff_neg_add_eq_vsub

namespace Set

open Pointwise

/- warning: set.singleton_vsub_self -> Set.singleton_vsub_self is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{succ u1} (Set.{u1} G) (VSub.vsub.{u1, u2} (Set.{u1} G) (Set.{u2} P) (Set.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T)) (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p) (Singleton.singleton.{u2, u2} P (Set.{u2} P) (Set.hasSingleton.{u2} P) p)) (Singleton.singleton.{u1, u1} G (Set.{u1} G) (Set.hasSingleton.{u1} G) (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))))))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{succ u2} (Set.{u2} G) (VSub.vsub.{u2, u1} (Set.{u2} G) (Set.{u1} P) (Set.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T)) (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p) (Singleton.singleton.{u1, u1} P (Set.{u1} P) (Set.instSingletonSet.{u1} P) p)) (Singleton.singleton.{u2, u2} G (Set.{u2} G) (Set.instSingletonSet.{u2} G) (OfNat.ofNat.{u2} G 0 (Zero.toOfNat0.{u2} G (NegZeroClass.toZero.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))))))
Case conversion may be inaccurate. Consider using '#align set.singleton_vsub_self Set.singleton_vsub_selfₓ'. -/
@[simp]
theorem singleton_vsub_self (p : P) : ({p} : Set P) -ᵥ {p} = {(0 : G)} := by
  rw [Set.singleton_vsub_singleton, vsub_self]
#align set.singleton_vsub_self Set.singleton_vsub_self

end Set

/- warning: vadd_vsub_vadd_cancel_right -> vadd_vsub_vadd_cancel_right is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] (v₁ : G) (v₂ : G) (p : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) v₁ p) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 T)) v₂ p)) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))) v₁ v₂)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] (v₁ : G) (v₂ : G) (p : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) v₁ p) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 T))) v₂ p)) (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1))) v₁ v₂)
Case conversion may be inaccurate. Consider using '#align vadd_vsub_vadd_cancel_right vadd_vsub_vadd_cancel_rightₓ'. -/
@[simp]
theorem vadd_vsub_vadd_cancel_right (v₁ v₂ : G) (p : P) : v₁ +ᵥ p -ᵥ (v₂ +ᵥ p) = v₁ - v₂ := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, vsub_self, add_zero]
#align vadd_vsub_vadd_cancel_right vadd_vsub_vadd_cancel_right

/- warning: vsub_left_cancel -> vsub_left_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P} {p : P}, (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p2 p)) -> (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P} {p : P}, (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p2 p)) -> (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_left_cancel vsub_left_cancelₓ'. -/
/-- If the same point subtracted from two points produces equal
results, those points are equal. -/
theorem vsub_left_cancel {p1 p2 p : P} (h : p1 -ᵥ p = p2 -ᵥ p) : p1 = p2 := by
  rwa [← sub_eq_zero, vsub_sub_vsub_cancel_right, vsub_eq_zero_iff_eq] at h
#align vsub_left_cancel vsub_left_cancel

/- warning: vsub_left_cancel_iff -> vsub_left_cancel_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P} {p : P}, Iff (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p1 p) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p2 p)) (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P} {p : P}, Iff (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p1 p) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p2 p)) (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_left_cancel_iff vsub_left_cancel_iffₓ'. -/
/-- The same point subtracted from two points produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_left_cancel_iff {p1 p2 p : P} : p1 -ᵥ p = p2 -ᵥ p ↔ p1 = p2 :=
  ⟨vsub_left_cancel, fun h => h ▸ rfl⟩
#align vsub_left_cancel_iff vsub_left_cancel_iff

#print vsub_left_injective /-
/-- Subtracting the point `p` is an injective function. -/
theorem vsub_left_injective (p : P) : Function.Injective ((· -ᵥ p) : P → G) := fun p2 p3 =>
  vsub_left_cancel
#align vsub_left_injective vsub_left_injective
-/

/- warning: vsub_right_cancel -> vsub_right_cancel is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P} {p : P}, (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p p1) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p p2)) -> (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P} {p : P}, (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p p1) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p p2)) -> (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_right_cancel vsub_right_cancelₓ'. -/
/-- If subtracting two points from the same point produces equal
results, those points are equal. -/
theorem vsub_right_cancel {p1 p2 p : P} (h : p -ᵥ p1 = p -ᵥ p2) : p1 = p2 :=
  by
  refine' vadd_left_cancel (p -ᵥ p2) _
  rw [vsub_vadd, ← h, vsub_vadd]
#align vsub_right_cancel vsub_right_cancel

/- warning: vsub_right_cancel_iff -> vsub_right_cancel_iff is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [T : AddTorsor.{u1, u2} G P _inst_1] {p1 : P} {p2 : P} {p : P}, Iff (Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p p1) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 T) p p2)) (Eq.{succ u2} P p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [T : AddTorsor.{u2, u1} G P _inst_1] {p1 : P} {p2 : P} {p : P}, Iff (Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p p1) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 T) p p2)) (Eq.{succ u1} P p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_right_cancel_iff vsub_right_cancel_iffₓ'. -/
/-- Subtracting two points from the same point produces equal results
if and only if those points are equal. -/
@[simp]
theorem vsub_right_cancel_iff {p1 p2 p : P} : p -ᵥ p1 = p -ᵥ p2 ↔ p1 = p2 :=
  ⟨vsub_right_cancel, fun h => h ▸ rfl⟩
#align vsub_right_cancel_iff vsub_right_cancel_iff

#print vsub_right_injective /-
/-- Subtracting a point from the point `p` is an injective
function. -/
theorem vsub_right_injective (p : P) : Function.Injective ((· -ᵥ ·) p : P → G) := fun p2 p3 =>
  vsub_right_cancel
#align vsub_right_injective vsub_right_injective
-/

end General

section comm

variable {G : Type _} {P : Type _} [AddCommGroup G] [AddTorsor G P]

include G

/- warning: vsub_sub_vsub_cancel_left -> vsub_sub_vsub_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1)] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p3 p2) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p3 p1)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddCommGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1)] (p1 : P) (p2 : P) (p3 : P), Eq.{succ u2} G (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_1)))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p3 p2) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p3 p1)) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p1 p2)
Case conversion may be inaccurate. Consider using '#align vsub_sub_vsub_cancel_left vsub_sub_vsub_cancel_leftₓ'. -/
/-- Cancellation subtracting the results of two subtractions. -/
@[simp]
theorem vsub_sub_vsub_cancel_left (p1 p2 p3 : P) : p3 -ᵥ p2 - (p3 -ᵥ p1) = p1 -ᵥ p2 := by
  rw [sub_eq_add_neg, neg_vsub_eq_vsub_rev, add_comm, vsub_add_vsub_cancel]
#align vsub_sub_vsub_cancel_left vsub_sub_vsub_cancel_left

/- warning: vadd_vsub_vadd_cancel_left -> vadd_vsub_vadd_cancel_left is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1)] (v : G) (p1 : P) (p2 : P), Eq.{succ u1} G (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2)) v p1) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2)) v p2)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p1 p2)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddCommGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1)] (v : G) (p1 : P) (p2 : P), Eq.{succ u2} G (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_1))) (AddTorsor.toAddAction.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2))) v p1) (HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_1))) (AddTorsor.toAddAction.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2))) v p2)) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p1 p2)
Case conversion may be inaccurate. Consider using '#align vadd_vsub_vadd_cancel_left vadd_vsub_vadd_cancel_leftₓ'. -/
@[simp]
theorem vadd_vsub_vadd_cancel_left (v : G) (p1 p2 : P) : v +ᵥ p1 -ᵥ (v +ᵥ p2) = p1 -ᵥ p2 := by
  rw [vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub_cancel']
#align vadd_vsub_vadd_cancel_left vadd_vsub_vadd_cancel_left

#print vsub_vadd_comm /-
theorem vsub_vadd_comm (p1 p2 p3 : P) : (p1 -ᵥ p2 : G) +ᵥ p3 = p3 -ᵥ p2 +ᵥ p1 :=
  by
  rw [← @vsub_eq_zero_iff_eq G, vadd_vsub_assoc, vsub_vadd_eq_vsub_sub]
  simp
#align vsub_vadd_comm vsub_vadd_comm
-/

/- warning: vadd_eq_vadd_iff_sub_eq_vsub -> vadd_eq_vadd_iff_sub_eq_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1)] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P}, Iff (Eq.{succ u2} P (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2)) v₁ p₁) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2)) v₂ p₂)) (Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) v₂ v₁) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₁ p₂))
but is expected to have type
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1)] {v₁ : G} {v₂ : G} {p₁ : P} {p₂ : P}, Iff (Eq.{succ u2} P (HVAdd.hVAdd.{u1, u2, u2} G P P (instHVAdd.{u1, u2} G P (AddAction.toVAdd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2))) v₁ p₁) (HVAdd.hVAdd.{u1, u2, u2} G P P (instHVAdd.{u1, u2} G P (AddAction.toVAdd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1))) (AddTorsor.toAddAction.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2))) v₂ p₂)) (Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) v₂ v₁) (VSub.vsub.{u1, u2} G P (AddTorsor.toVSub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₁ p₂))
Case conversion may be inaccurate. Consider using '#align vadd_eq_vadd_iff_sub_eq_vsub vadd_eq_vadd_iff_sub_eq_vsubₓ'. -/
theorem vadd_eq_vadd_iff_sub_eq_vsub {v₁ v₂ : G} {p₁ p₂ : P} :
    v₁ +ᵥ p₁ = v₂ +ᵥ p₂ ↔ v₂ - v₁ = p₁ -ᵥ p₂ := by
  rw [vadd_eq_vadd_iff_neg_add_eq_vsub, neg_add_eq_sub]
#align vadd_eq_vadd_iff_sub_eq_vsub vadd_eq_vadd_iff_sub_eq_vsub

/- warning: vsub_sub_vsub_comm -> vsub_sub_vsub_comm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddCommGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1)] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), Eq.{succ u1} G (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₁ p₂) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₃ p₄)) (HSub.hSub.{u1, u1, u1} G G G (instHSub.{u1} G (SubNegMonoid.toHasSub.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_1)))) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₁ p₃) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_1) _inst_2) p₂ p₄))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddCommGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1)] (p₁ : P) (p₂ : P) (p₃ : P) (p₄ : P), Eq.{succ u2} G (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_1)))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p₁ p₂) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p₃ p₄)) (HSub.hSub.{u2, u2, u2} G G G (instHSub.{u2} G (SubNegMonoid.toSub.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_1)))) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p₁ p₃) (VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_1) _inst_2) p₂ p₄))
Case conversion may be inaccurate. Consider using '#align vsub_sub_vsub_comm vsub_sub_vsub_commₓ'. -/
theorem vsub_sub_vsub_comm (p₁ p₂ p₃ p₄ : P) : p₁ -ᵥ p₂ - (p₃ -ᵥ p₄) = p₁ -ᵥ p₃ - (p₂ -ᵥ p₄) := by
  rw [← vsub_vadd_eq_vsub_sub, vsub_vadd_comm, vsub_vadd_eq_vsub_sub]
#align vsub_sub_vsub_comm vsub_sub_vsub_comm

end comm

namespace Prod

variable {G : Type _} {P : Type _} {G' : Type _} {P' : Type _} [AddGroup G] [AddGroup G']
  [AddTorsor G P] [AddTorsor G' P']

instance : AddTorsor (G × G') (P × P')
    where
  vadd v p := (v.1 +ᵥ p.1, v.2 +ᵥ p.2)
  zero_vadd p := by simp
  add_vadd := by simp [add_vadd]
  vsub p₁ p₂ := (p₁.1 -ᵥ p₂.1, p₁.2 -ᵥ p₂.2)
  Nonempty := Prod.nonempty
  vsub_vadd' p₁ p₂ := show (p₁.1 -ᵥ p₂.1 +ᵥ p₂.1, _) = p₁ by simp
  vadd_vsub' v p := show (v.1 +ᵥ p.1 -ᵥ p.1, v.2 +ᵥ p.2 -ᵥ p.2) = v by simp

/- warning: prod.fst_vadd -> Prod.fst_vadd is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (v : Prod.{u1, u3} G G') (p : Prod.{u2, u4} P P'), Eq.{succ u2} P (Prod.fst.{u2, u4} P P' (VAdd.vadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddAction.toHasVadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (SubNegMonoid.toAddMonoid.{max u1 u3} (Prod.{u1, u3} G G') (AddGroup.toSubNegMonoid.{max u1 u3} (Prod.{u1, u3} G G') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2))) (AddTorsor.toAddAction.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4))) v p)) (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 _inst_3)) (Prod.fst.{u1, u3} G G' v) (Prod.fst.{u2, u4} P P' p))
but is expected to have type
  forall {G : Type.{u4}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u1}} [_inst_1 : AddGroup.{u4} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u4, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u1} G' P' _inst_2] (v : Prod.{u4, u3} G G') (p : Prod.{u2, u1} P P'), Eq.{succ u2} P (Prod.fst.{u2, u1} P P' (HVAdd.hVAdd.{max u4 u3, max u2 u1, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.{u2, u1} P P') (instHVAdd.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (AddAction.toVAdd.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.instAddMonoidSum.{u4, u3} G G' (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)) (SubNegMonoid.toAddMonoid.{u3} G' (AddGroup.toSubNegMonoid.{u3} G' _inst_2))) (AddTorsor.toAddAction.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.instAddGroupSum.{u4, u3} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u4, u2, u3, u1} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)))) v p)) (HVAdd.hVAdd.{u4, u2, u2} G P P (instHVAdd.{u4, u2} G P (AddAction.toVAdd.{u4, u2} G P (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)) (AddTorsor.toAddAction.{u4, u2} G P _inst_1 _inst_3))) (Prod.fst.{u4, u3} G G' v) (Prod.fst.{u2, u1} P P' p))
Case conversion may be inaccurate. Consider using '#align prod.fst_vadd Prod.fst_vaddₓ'. -/
@[simp]
theorem fst_vadd (v : G × G') (p : P × P') : (v +ᵥ p).1 = v.1 +ᵥ p.1 :=
  rfl
#align prod.fst_vadd Prod.fst_vadd

/- warning: prod.snd_vadd -> Prod.snd_vadd is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (v : Prod.{u1, u3} G G') (p : Prod.{u2, u4} P P'), Eq.{succ u4} P' (Prod.snd.{u2, u4} P P' (VAdd.vadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddAction.toHasVadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (SubNegMonoid.toAddMonoid.{max u1 u3} (Prod.{u1, u3} G G') (AddGroup.toSubNegMonoid.{max u1 u3} (Prod.{u1, u3} G G') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2))) (AddTorsor.toAddAction.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4))) v p)) (VAdd.vadd.{u3, u4} G' P' (AddAction.toHasVadd.{u3, u4} G' P' (SubNegMonoid.toAddMonoid.{u3} G' (AddGroup.toSubNegMonoid.{u3} G' _inst_2)) (AddTorsor.toAddAction.{u3, u4} G' P' _inst_2 _inst_4)) (Prod.snd.{u1, u3} G G' v) (Prod.snd.{u2, u4} P P' p))
but is expected to have type
  forall {G : Type.{u4}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u1}} [_inst_1 : AddGroup.{u4} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u4, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u1} G' P' _inst_2] (v : Prod.{u4, u3} G G') (p : Prod.{u2, u1} P P'), Eq.{succ u1} P' (Prod.snd.{u2, u1} P P' (HVAdd.hVAdd.{max u4 u3, max u2 u1, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.{u2, u1} P P') (instHVAdd.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (AddAction.toVAdd.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.instAddMonoidSum.{u4, u3} G G' (SubNegMonoid.toAddMonoid.{u4} G (AddGroup.toSubNegMonoid.{u4} G _inst_1)) (SubNegMonoid.toAddMonoid.{u3} G' (AddGroup.toSubNegMonoid.{u3} G' _inst_2))) (AddTorsor.toAddAction.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u2, u1} P P') (Prod.instAddGroupSum.{u4, u3} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u4, u2, u3, u1} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)))) v p)) (HVAdd.hVAdd.{u3, u1, u1} G' P' P' (instHVAdd.{u3, u1} G' P' (AddAction.toVAdd.{u3, u1} G' P' (SubNegMonoid.toAddMonoid.{u3} G' (AddGroup.toSubNegMonoid.{u3} G' _inst_2)) (AddTorsor.toAddAction.{u3, u1} G' P' _inst_2 _inst_4))) (Prod.snd.{u4, u3} G G' v) (Prod.snd.{u2, u1} P P' p))
Case conversion may be inaccurate. Consider using '#align prod.snd_vadd Prod.snd_vaddₓ'. -/
@[simp]
theorem snd_vadd (v : G × G') (p : P × P') : (v +ᵥ p).2 = v.2 +ᵥ p.2 :=
  rfl
#align prod.snd_vadd Prod.snd_vadd

/- warning: prod.mk_vadd_mk -> Prod.mk_vadd_mk is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (v : G) (v' : G') (p : P) (p' : P'), Eq.{succ (max u2 u4)} (Prod.{u2, u4} P P') (VAdd.vadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddAction.toHasVadd.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (SubNegMonoid.toAddMonoid.{max u1 u3} (Prod.{u1, u3} G G') (AddGroup.toSubNegMonoid.{max u1 u3} (Prod.{u1, u3} G G') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2))) (AddTorsor.toAddAction.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4))) (Prod.mk.{u1, u3} G G' v v') (Prod.mk.{u2, u4} P P' p p')) (Prod.mk.{u2, u4} P P' (VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 _inst_3)) v p) (VAdd.vadd.{u3, u4} G' P' (AddAction.toHasVadd.{u3, u4} G' P' (SubNegMonoid.toAddMonoid.{u3} G' (AddGroup.toSubNegMonoid.{u3} G' _inst_2)) (AddTorsor.toAddAction.{u3, u4} G' P' _inst_2 _inst_4)) v' p'))
but is expected to have type
  forall {G : Type.{u1}} {P : Type.{u4}} {G' : Type.{u2}} {P' : Type.{u3}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u2} G'] [_inst_3 : AddTorsor.{u1, u4} G P _inst_1] [_inst_4 : AddTorsor.{u2, u3} G' P' _inst_2] (v : G) (v' : G') (p : P) (p' : P'), Eq.{max (succ u4) (succ u3)} (Prod.{u4, u3} P P') (HVAdd.hVAdd.{max u2 u1, max u3 u4, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (Prod.{u4, u3} P P') (instHVAdd.{max u1 u2, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (AddAction.toVAdd.{max u1 u2, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (Prod.instAddMonoidSum.{u1, u2} G G' (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (SubNegMonoid.toAddMonoid.{u2} G' (AddGroup.toSubNegMonoid.{u2} G' _inst_2))) (AddTorsor.toAddAction.{max u1 u2, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (Prod.instAddGroupSum.{u1, u2} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u1, u4, u2, u3} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)))) (Prod.mk.{u1, u2} G G' v v') (Prod.mk.{u4, u3} P P' p p')) (Prod.mk.{u4, u3} P P' (HVAdd.hVAdd.{u1, u4, u4} G P P (instHVAdd.{u1, u4} G P (AddAction.toVAdd.{u1, u4} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u4} G P _inst_1 _inst_3))) v p) (HVAdd.hVAdd.{u2, u3, u3} G' P' P' (instHVAdd.{u2, u3} G' P' (AddAction.toVAdd.{u2, u3} G' P' (SubNegMonoid.toAddMonoid.{u2} G' (AddGroup.toSubNegMonoid.{u2} G' _inst_2)) (AddTorsor.toAddAction.{u2, u3} G' P' _inst_2 _inst_4))) v' p'))
Case conversion may be inaccurate. Consider using '#align prod.mk_vadd_mk Prod.mk_vadd_mkₓ'. -/
@[simp]
theorem mk_vadd_mk (v : G) (v' : G') (p : P) (p' : P') : (v, v') +ᵥ (p, p') = (v +ᵥ p, v' +ᵥ p') :=
  rfl
#align prod.mk_vadd_mk Prod.mk_vadd_mk

/- warning: prod.fst_vsub -> Prod.fst_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (p₁ : Prod.{u2, u4} P P') (p₂ : Prod.{u2, u4} P P'), Eq.{succ u1} G (Prod.fst.{u1, u3} G G' (VSub.vsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddTorsor.toHasVsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) p₁ p₂)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 _inst_3) (Prod.fst.{u2, u4} P P' p₁) (Prod.fst.{u2, u4} P P' p₂))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u4}} {G' : Type.{u1}} {P' : Type.{u3}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddGroup.{u1} G'] [_inst_3 : AddTorsor.{u2, u4} G P _inst_1] [_inst_4 : AddTorsor.{u1, u3} G' P' _inst_2] (p₁ : Prod.{u4, u3} P P') (p₂ : Prod.{u4, u3} P P'), Eq.{succ u2} G (Prod.fst.{u2, u1} G G' (VSub.vsub.{max u2 u1, max u4 u3} (Prod.{u2, u1} G G') (Prod.{u4, u3} P P') (AddTorsor.toVSub.{max u2 u1, max u4 u3} (Prod.{u2, u1} G G') (Prod.{u4, u3} P P') (Prod.instAddGroupSum.{u2, u1} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u2, u4, u1, u3} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) p₁ p₂)) (VSub.vsub.{u2, u4} G P (AddTorsor.toVSub.{u2, u4} G P _inst_1 _inst_3) (Prod.fst.{u4, u3} P P' p₁) (Prod.fst.{u4, u3} P P' p₂))
Case conversion may be inaccurate. Consider using '#align prod.fst_vsub Prod.fst_vsubₓ'. -/
@[simp]
theorem fst_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').1 = p₁.1 -ᵥ p₂.1 :=
  rfl
#align prod.fst_vsub Prod.fst_vsub

/- warning: prod.snd_vsub -> Prod.snd_vsub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (p₁ : Prod.{u2, u4} P P') (p₂ : Prod.{u2, u4} P P'), Eq.{succ u3} G' (Prod.snd.{u1, u3} G G' (VSub.vsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddTorsor.toHasVsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) p₁ p₂)) (VSub.vsub.{u3, u4} G' P' (AddTorsor.toHasVsub.{u3, u4} G' P' _inst_2 _inst_4) (Prod.snd.{u2, u4} P P' p₁) (Prod.snd.{u2, u4} P P' p₂))
but is expected to have type
  forall {G : Type.{u1}} {P : Type.{u4}} {G' : Type.{u2}} {P' : Type.{u3}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u2} G'] [_inst_3 : AddTorsor.{u1, u4} G P _inst_1] [_inst_4 : AddTorsor.{u2, u3} G' P' _inst_2] (p₁ : Prod.{u4, u3} P P') (p₂ : Prod.{u4, u3} P P'), Eq.{succ u2} G' (Prod.snd.{u1, u2} G G' (VSub.vsub.{max u1 u2, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (AddTorsor.toVSub.{max u1 u2, max u4 u3} (Prod.{u1, u2} G G') (Prod.{u4, u3} P P') (Prod.instAddGroupSum.{u1, u2} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u1, u4, u2, u3} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) p₁ p₂)) (VSub.vsub.{u2, u3} G' P' (AddTorsor.toVSub.{u2, u3} G' P' _inst_2 _inst_4) (Prod.snd.{u4, u3} P P' p₁) (Prod.snd.{u4, u3} P P' p₂))
Case conversion may be inaccurate. Consider using '#align prod.snd_vsub Prod.snd_vsubₓ'. -/
@[simp]
theorem snd_vsub (p₁ p₂ : P × P') : (p₁ -ᵥ p₂ : G × G').2 = p₁.2 -ᵥ p₂.2 :=
  rfl
#align prod.snd_vsub Prod.snd_vsub

/- warning: prod.mk_vsub_mk -> Prod.mk_vsub_mk is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} {G' : Type.{u3}} {P' : Type.{u4}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u1, u2} G P _inst_1] [_inst_4 : AddTorsor.{u3, u4} G' P' _inst_2] (p₁ : P) (p₂ : P) (p₁' : P') (p₂' : P'), Eq.{max (succ u1) (succ u3)} (Prod.{u1, u3} G G') (VSub.vsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (AddTorsor.toHasVsub.{max u1 u3, max u2 u4} (Prod.{u1, u3} G G') (Prod.{u2, u4} P P') (Prod.addGroup.{u1, u3} G G' _inst_1 _inst_2) (Prod.addTorsor.{u1, u2, u3, u4} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) (Prod.mk.{u2, u4} P P' p₁ p₁') (Prod.mk.{u2, u4} P P' p₂ p₂')) (Prod.mk.{u1, u3} G G' (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 _inst_3) p₁ p₂) (VSub.vsub.{u3, u4} G' P' (AddTorsor.toHasVsub.{u3, u4} G' P' _inst_2 _inst_4) p₁' p₂'))
but is expected to have type
  forall {G : Type.{u4}} {P : Type.{u1}} {G' : Type.{u3}} {P' : Type.{u2}} [_inst_1 : AddGroup.{u4} G] [_inst_2 : AddGroup.{u3} G'] [_inst_3 : AddTorsor.{u4, u1} G P _inst_1] [_inst_4 : AddTorsor.{u3, u2} G' P' _inst_2] (p₁ : P) (p₂ : P) (p₁' : P') (p₂' : P'), Eq.{max (succ u4) (succ u3)} (Prod.{u4, u3} G G') (VSub.vsub.{max u4 u3, max u2 u1} (Prod.{u4, u3} G G') (Prod.{u1, u2} P P') (AddTorsor.toVSub.{max u4 u3, max u1 u2} (Prod.{u4, u3} G G') (Prod.{u1, u2} P P') (Prod.instAddGroupSum.{u4, u3} G G' _inst_1 _inst_2) (Prod.instAddTorsorProdProdInstAddGroupSum.{u4, u1, u3, u2} G P G' P' _inst_1 _inst_2 _inst_3 _inst_4)) (Prod.mk.{u1, u2} P P' p₁ p₁') (Prod.mk.{u1, u2} P P' p₂ p₂')) (Prod.mk.{u4, u3} G G' (VSub.vsub.{u4, u1} G P (AddTorsor.toVSub.{u4, u1} G P _inst_1 _inst_3) p₁ p₂) (VSub.vsub.{u3, u2} G' P' (AddTorsor.toVSub.{u3, u2} G' P' _inst_2 _inst_4) p₁' p₂'))
Case conversion may be inaccurate. Consider using '#align prod.mk_vsub_mk Prod.mk_vsub_mkₓ'. -/
@[simp]
theorem mk_vsub_mk (p₁ p₂ : P) (p₁' p₂' : P') :
    ((p₁, p₁') -ᵥ (p₂, p₂') : G × G') = (p₁ -ᵥ p₂, p₁' -ᵥ p₂') :=
  rfl
#align prod.mk_vsub_mk Prod.mk_vsub_mk

end Prod

namespace Pi

universe u v w

variable {I : Type u} {fg : I → Type v} [∀ i, AddGroup (fg i)] {fp : I → Type w}

open AddAction AddTorsor

/-- A product of `add_torsor`s is an `add_torsor`. -/
instance [T : ∀ i, AddTorsor (fg i) (fp i)] : AddTorsor (∀ i, fg i) (∀ i, fp i)
    where
  vadd g p i := g i +ᵥ p i
  zero_vadd p := funext fun i => zero_vadd (fg i) (p i)
  add_vadd g₁ g₂ p := funext fun i => add_vadd (g₁ i) (g₂ i) (p i)
  vsub p₁ p₂ i := p₁ i -ᵥ p₂ i
  Nonempty := ⟨fun i => Classical.choice (T i).Nonempty⟩
  vsub_vadd' p₁ p₂ := funext fun i => vsub_vadd (p₁ i) (p₂ i)
  vadd_vsub' g p := funext fun i => vadd_vsub (g i) (p i)

end Pi

namespace Equiv

variable {G : Type _} {P : Type _} [AddGroup G] [AddTorsor G P]

include G

#print Equiv.vaddConst /-
/-- `v ↦ v +ᵥ p` as an equivalence. -/
def vaddConst (p : P) : G ≃ P where
  toFun v := v +ᵥ p
  invFun p' := p' -ᵥ p
  left_inv v := vadd_vsub _ _
  right_inv p' := vsub_vadd _ _
#align equiv.vadd_const Equiv.vaddConst
-/

/- warning: equiv.coe_vadd_const -> Equiv.coe_vaddConst is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{max (succ u1) (succ u2)} (G -> P) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} G P) (fun (_x : Equiv.{succ u1, succ u2} G P) => G -> P) (Equiv.hasCoeToFun.{succ u1, succ u2} G P) (Equiv.vaddConst.{u1, u2} G P _inst_1 _inst_2 p)) (fun (v : G) => VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 _inst_2)) v p)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : G), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : G) => P) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} G P) G (fun (_x : G) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : G) => P) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} G P) (Equiv.vaddConst.{u2, u1} G P _inst_1 _inst_2 p)) (fun (v : G) => HVAdd.hVAdd.{u2, u1, u1} G P ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : G) => P) v) (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 _inst_2))) v p)
Case conversion may be inaccurate. Consider using '#align equiv.coe_vadd_const Equiv.coe_vaddConstₓ'. -/
@[simp]
theorem coe_vaddConst (p : P) : ⇑(vaddConst p) = fun v => v +ᵥ p :=
  rfl
#align equiv.coe_vadd_const Equiv.coe_vaddConst

/- warning: equiv.coe_vadd_const_symm -> Equiv.coe_vaddConst_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (P -> G) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} P G) (fun (_x : Equiv.{succ u2, succ u1} P G) => P -> G) (Equiv.hasCoeToFun.{succ u2, succ u1} P G) (Equiv.symm.{succ u1, succ u2} G P (Equiv.vaddConst.{u1, u2} G P _inst_1 _inst_2 p))) (fun (p' : P) => VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 _inst_2) p' p)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : P), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => G) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} P G) P (fun (_x : P) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => G) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} P G) (Equiv.symm.{succ u2, succ u1} G P (Equiv.vaddConst.{u2, u1} G P _inst_1 _inst_2 p))) (fun (p' : P) => VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 _inst_2) p' p)
Case conversion may be inaccurate. Consider using '#align equiv.coe_vadd_const_symm Equiv.coe_vaddConst_symmₓ'. -/
@[simp]
theorem coe_vaddConst_symm (p : P) : ⇑(vaddConst p).symm = fun p' => p' -ᵥ p :=
  rfl
#align equiv.coe_vadd_const_symm Equiv.coe_vaddConst_symm

#print Equiv.constVSub /-
/-- `p' ↦ p -ᵥ p'` as an equivalence. -/
def constVSub (p : P) : P ≃ G where
  toFun := (· -ᵥ ·) p
  invFun v := -v +ᵥ p
  left_inv p' := by simp
  right_inv v := by simp [vsub_vadd_eq_vsub_sub]
#align equiv.const_vsub Equiv.constVSub
-/

/- warning: equiv.coe_const_vsub -> Equiv.coe_constVSub is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (P -> G) (coeFn.{max 1 (max (succ u2) (succ u1)) (succ u1) (succ u2), max (succ u2) (succ u1)} (Equiv.{succ u2, succ u1} P G) (fun (_x : Equiv.{succ u2, succ u1} P G) => P -> G) (Equiv.hasCoeToFun.{succ u2, succ u1} P G) (Equiv.constVSub.{u1, u2} G P _inst_1 _inst_2 p)) (VSub.vsub.{u1, u2} G P (AddTorsor.toHasVsub.{u1, u2} G P _inst_1 _inst_2) p)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : P), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => G) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u1, succ u2} (Equiv.{succ u1, succ u2} P G) P (fun (_x : P) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => G) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u2} P G) (Equiv.constVSub.{u2, u1} G P _inst_1 _inst_2 p)) ((fun (x._@.Mathlib.Algebra.AddTorsor._hyg.2806 : P) (x._@.Mathlib.Algebra.AddTorsor._hyg.2808 : P) => VSub.vsub.{u2, u1} G P (AddTorsor.toVSub.{u2, u1} G P _inst_1 _inst_2) x._@.Mathlib.Algebra.AddTorsor._hyg.2806 x._@.Mathlib.Algebra.AddTorsor._hyg.2808) p)
Case conversion may be inaccurate. Consider using '#align equiv.coe_const_vsub Equiv.coe_constVSubₓ'. -/
@[simp]
theorem coe_constVSub (p : P) : ⇑(constVSub p) = (· -ᵥ ·) p :=
  rfl
#align equiv.coe_const_vsub Equiv.coe_constVSub

/- warning: equiv.coe_const_vsub_symm -> Equiv.coe_constVSub_symm is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (p : P), Eq.{max (succ u1) (succ u2)} (G -> P) (coeFn.{max 1 (max (succ u1) (succ u2)) (succ u2) (succ u1), max (succ u1) (succ u2)} (Equiv.{succ u1, succ u2} G P) (fun (_x : Equiv.{succ u1, succ u2} G P) => G -> P) (Equiv.hasCoeToFun.{succ u1, succ u2} G P) (Equiv.symm.{succ u2, succ u1} P G (Equiv.constVSub.{u1, u2} G P _inst_1 _inst_2 p))) (fun (v : G) => VAdd.vadd.{u1, u2} G P (AddAction.toHasVadd.{u1, u2} G P (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) (AddTorsor.toAddAction.{u1, u2} G P _inst_1 _inst_2)) (Neg.neg.{u1} G (SubNegMonoid.toHasNeg.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)) v) p)
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] (p : P), Eq.{max (succ u2) (succ u1)} (forall (ᾰ : G), (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : G) => P) ᾰ) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Equiv.{succ u2, succ u1} G P) G (fun (_x : G) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : G) => P) _x) (Equiv.instFunLikeEquiv.{succ u2, succ u1} G P) (Equiv.symm.{succ u1, succ u2} P G (Equiv.constVSub.{u2, u1} G P _inst_1 _inst_2 p))) (fun (v : G) => HVAdd.hVAdd.{u2, u1, u1} G P P (instHVAdd.{u2, u1} G P (AddAction.toVAdd.{u2, u1} G P (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)) (AddTorsor.toAddAction.{u2, u1} G P _inst_1 _inst_2))) (Neg.neg.{u2} G (NegZeroClass.toNeg.{u2} G (SubNegZeroMonoid.toNegZeroClass.{u2} G (SubtractionMonoid.toSubNegZeroMonoid.{u2} G (AddGroup.toSubtractionMonoid.{u2} G _inst_1)))) v) p)
Case conversion may be inaccurate. Consider using '#align equiv.coe_const_vsub_symm Equiv.coe_constVSub_symmₓ'. -/
@[simp]
theorem coe_constVSub_symm (p : P) : ⇑(constVSub p).symm = fun v => -v +ᵥ p :=
  rfl
#align equiv.coe_const_vsub_symm Equiv.coe_constVSub_symm

variable (P)

#print Equiv.constVAdd /-
/-- The permutation given by `p ↦ v +ᵥ p`. -/
def constVAdd (v : G) : Equiv.Perm P where
  toFun := (· +ᵥ ·) v
  invFun := (· +ᵥ ·) (-v)
  left_inv p := by simp [vadd_vadd]
  right_inv p := by simp [vadd_vadd]
#align equiv.const_vadd Equiv.constVAdd
-/

#print Equiv.coe_constVAdd /-
@[simp]
theorem coe_constVAdd (v : G) : ⇑(constVAdd P v) = (· +ᵥ ·) v :=
  rfl
#align equiv.coe_const_vadd Equiv.coe_constVAdd
-/

variable (G)

/- warning: equiv.const_vadd_zero -> Equiv.constVAdd_zero is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1], Eq.{succ u2} (Equiv.Perm.{succ u2} P) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 (OfNat.ofNat.{u1} G 0 (OfNat.mk.{u1} G 0 (Zero.zero.{u1} G (AddZeroClass.toHasZero.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))))) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} P) 1 (OfNat.mk.{u2} (Equiv.Perm.{succ u2} P) 1 (One.one.{u2} (Equiv.Perm.{succ u2} P) (MulOneClass.toHasOne.{u2} (Equiv.Perm.{succ u2} P) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} P) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} P) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.permGroup.{u2} P))))))))
but is expected to have type
  forall (G : Type.{u1}) (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1], Eq.{succ u2} (Equiv.Perm.{succ u2} P) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 (OfNat.ofNat.{u1} G 0 (Zero.toOfNat0.{u1} G (NegZeroClass.toZero.{u1} G (SubNegZeroMonoid.toNegZeroClass.{u1} G (SubtractionMonoid.toSubNegZeroMonoid.{u1} G (AddGroup.toSubtractionMonoid.{u1} G _inst_1))))))) (OfNat.ofNat.{u2} (Equiv.Perm.{succ u2} P) 1 (One.toOfNat1.{u2} (Equiv.Perm.{succ u2} P) (InvOneClass.toOne.{u2} (Equiv.Perm.{succ u2} P) (DivInvOneMonoid.toInvOneClass.{u2} (Equiv.Perm.{succ u2} P) (DivisionMonoid.toDivInvOneMonoid.{u2} (Equiv.Perm.{succ u2} P) (Group.toDivisionMonoid.{u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.permGroup.{u2} P)))))))
Case conversion may be inaccurate. Consider using '#align equiv.const_vadd_zero Equiv.constVAdd_zeroₓ'. -/
@[simp]
theorem constVAdd_zero : constVAdd P (0 : G) = 1 :=
  ext <| zero_vadd G
#align equiv.const_vadd_zero Equiv.constVAdd_zero

variable {G}

/- warning: equiv.const_vadd_add -> Equiv.constVAdd_add is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (v₁ : G) (v₂ : G), Eq.{succ u2} (Equiv.Perm.{succ u2} P) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) v₁ v₂)) (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.{succ u2} P) (Equiv.Perm.{succ u2} P) (instHMul.{u2} (Equiv.Perm.{succ u2} P) (MulOneClass.toHasMul.{u2} (Equiv.Perm.{succ u2} P) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} P) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} P) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.permGroup.{u2} P)))))) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 v₁) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 v₂))
but is expected to have type
  forall {G : Type.{u1}} (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] (v₁ : G) (v₂ : G), Eq.{succ u2} (Equiv.Perm.{succ u2} P) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 (HAdd.hAdd.{u1, u1, u1} G G G (instHAdd.{u1} G (AddZeroClass.toAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1))))) v₁ v₂)) (HMul.hMul.{u2, u2, u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.{succ u2} P) (Equiv.Perm.{succ u2} P) (instHMul.{u2} (Equiv.Perm.{succ u2} P) (MulOneClass.toMul.{u2} (Equiv.Perm.{succ u2} P) (Monoid.toMulOneClass.{u2} (Equiv.Perm.{succ u2} P) (DivInvMonoid.toMonoid.{u2} (Equiv.Perm.{succ u2} P) (Group.toDivInvMonoid.{u2} (Equiv.Perm.{succ u2} P) (Equiv.Perm.permGroup.{u2} P)))))) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 v₁) (Equiv.constVAdd.{u1, u2} G P _inst_1 _inst_2 v₂))
Case conversion may be inaccurate. Consider using '#align equiv.const_vadd_add Equiv.constVAdd_addₓ'. -/
@[simp]
theorem constVAdd_add (v₁ v₂ : G) : constVAdd P (v₁ + v₂) = constVAdd P v₁ * constVAdd P v₂ :=
  ext <| add_vadd v₁ v₂
#align equiv.const_vadd_add Equiv.constVAdd_add

#print Equiv.constVAddHom /-
/-- `equiv.const_vadd` as a homomorphism from `multiplicative G` to `equiv.perm P` -/
def constVAddHom : Multiplicative G →* Equiv.Perm P
    where
  toFun v := constVAdd P v.toAdd
  map_one' := constVAdd_zero G P
  map_mul' := constVAdd_add P
#align equiv.const_vadd_hom Equiv.constVAddHom
-/

variable {P}

open _Root_.Function

#print Equiv.pointReflection /-
/-- Point reflection in `x` as a permutation. -/
def pointReflection (x : P) : Perm P :=
  (constVSub x).trans (vaddConst x)
#align equiv.point_reflection Equiv.pointReflection
-/

#print Equiv.pointReflection_apply /-
theorem pointReflection_apply (x y : P) : pointReflection x y = x -ᵥ y +ᵥ x :=
  rfl
#align equiv.point_reflection_apply Equiv.pointReflection_apply
-/

#print Equiv.pointReflection_symm /-
@[simp]
theorem pointReflection_symm (x : P) : (pointReflection x).symm = pointReflection x :=
  ext <| by simp [point_reflection]
#align equiv.point_reflection_symm Equiv.pointReflection_symm
-/

#print Equiv.pointReflection_self /-
@[simp]
theorem pointReflection_self (x : P) : pointReflection x x = x :=
  vsub_vadd _ _
#align equiv.point_reflection_self Equiv.pointReflection_self
-/

#print Equiv.pointReflection_involutive /-
theorem pointReflection_involutive (x : P) : Involutive (pointReflection x : P → P) := fun y =>
  (Equiv.apply_eq_iff_eq_symm_apply _).2 <| by rw [point_reflection_symm]
#align equiv.point_reflection_involutive Equiv.pointReflection_involutive
-/

/- warning: equiv.point_reflection_fixed_iff_of_injective_bit0 -> Equiv.pointReflection_fixed_iff_of_injective_bit0 is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1] {x : P} {y : P}, (Function.Injective.{succ u1, succ u1} G G (bit0.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G _inst_1)))))) -> (Iff (Eq.{succ u2} P (coeFn.{succ u2, succ u2} (Equiv.Perm.{succ u2} P) (fun (_x : Equiv.{succ u2, succ u2} P P) => P -> P) (Equiv.hasCoeToFun.{succ u2, succ u2} P P) (Equiv.pointReflection.{u1, u2} G P _inst_1 _inst_2 x) y) y) (Eq.{succ u2} P y x))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1] {x : P} {y : P}, (Function.Injective.{succ u2, succ u2} G G (bit0.{u2} G (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G _inst_1)))))) -> (Iff (Eq.{succ u1} ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => P) y) (FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} P) P (fun (_x : P) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => P) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} P P) (Equiv.pointReflection.{u2, u1} G P _inst_1 _inst_2 x) y) y) (Eq.{succ u1} P y x))
Case conversion may be inaccurate. Consider using '#align equiv.point_reflection_fixed_iff_of_injective_bit0 Equiv.pointReflection_fixed_iff_of_injective_bit0ₓ'. -/
/-- `x` is the only fixed point of `point_reflection x`. This lemma requires
`x + x = y + y ↔ x = y`. There is no typeclass to use here, so we add it as an explicit argument. -/
theorem pointReflection_fixed_iff_of_injective_bit0 {x y : P} (h : Injective (bit0 : G → G)) :
    pointReflection x y = y ↔ y = x := by
  rw [point_reflection_apply, eq_comm, eq_vadd_iff_vsub_eq, ← neg_vsub_eq_vsub_rev,
    neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero, h.eq_iff, vsub_eq_zero_iff_eq, eq_comm]
#align equiv.point_reflection_fixed_iff_of_injective_bit0 Equiv.pointReflection_fixed_iff_of_injective_bit0

omit G

/- warning: equiv.injective_point_reflection_left_of_injective_bit0 -> Equiv.injective_pointReflection_left_of_injective_bit0 is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} {P : Type.{u2}} [_inst_3 : AddCommGroup.{u1} G] [_inst_4 : AddTorsor.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_3)], (Function.Injective.{succ u1, succ u1} G G (bit0.{u1} G (AddZeroClass.toHasAdd.{u1} G (AddMonoid.toAddZeroClass.{u1} G (SubNegMonoid.toAddMonoid.{u1} G (AddGroup.toSubNegMonoid.{u1} G (AddCommGroup.toAddGroup.{u1} G _inst_3))))))) -> (forall (y : P), Function.Injective.{succ u2, succ u2} P P (fun (x : P) => coeFn.{succ u2, succ u2} (Equiv.Perm.{succ u2} P) (fun (_x : Equiv.{succ u2, succ u2} P P) => P -> P) (Equiv.hasCoeToFun.{succ u2, succ u2} P P) (Equiv.pointReflection.{u1, u2} G P (AddCommGroup.toAddGroup.{u1} G _inst_3) _inst_4 x) y))
but is expected to have type
  forall {G : Type.{u2}} {P : Type.{u1}} [_inst_3 : AddCommGroup.{u2} G] [_inst_4 : AddTorsor.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_3)], (Function.Injective.{succ u2, succ u2} G G (bit0.{u2} G (AddZeroClass.toAdd.{u2} G (AddMonoid.toAddZeroClass.{u2} G (SubNegMonoid.toAddMonoid.{u2} G (AddGroup.toSubNegMonoid.{u2} G (AddCommGroup.toAddGroup.{u2} G _inst_3))))))) -> (forall (y : P), Function.Injective.{succ u1, succ u1} P ((fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => P) y) (fun (x : P) => FunLike.coe.{succ u1, succ u1, succ u1} (Equiv.Perm.{succ u1} P) P (fun (_x : P) => (fun (x._@.Mathlib.Logic.Equiv.Defs._hyg.805 : P) => P) _x) (Equiv.instFunLikeEquiv.{succ u1, succ u1} P P) (Equiv.pointReflection.{u2, u1} G P (AddCommGroup.toAddGroup.{u2} G _inst_3) _inst_4 x) y))
Case conversion may be inaccurate. Consider using '#align equiv.injective_point_reflection_left_of_injective_bit0 Equiv.injective_pointReflection_left_of_injective_bit0ₓ'. -/
theorem injective_pointReflection_left_of_injective_bit0 {G P : Type _} [AddCommGroup G]
    [AddTorsor G P] (h : Injective (bit0 : G → G)) (y : P) :
    Injective fun x : P => pointReflection x y :=
  fun x₁ x₂ (hy : pointReflection x₁ y = pointReflection x₂ y) => by
  rwa [point_reflection_apply, point_reflection_apply, vadd_eq_vadd_iff_sub_eq_vsub,
    vsub_sub_vsub_cancel_right, ← neg_vsub_eq_vsub_rev, neg_eq_iff_add_eq_zero, ← bit0, ← bit0_zero,
    h.eq_iff, vsub_eq_zero_iff_eq] at hy
#align equiv.injective_point_reflection_left_of_injective_bit0 Equiv.injective_pointReflection_left_of_injective_bit0

end Equiv

/- warning: add_torsor.subsingleton_iff -> AddTorsor.subsingleton_iff is a dubious translation:
lean 3 declaration is
  forall (G : Type.{u1}) (P : Type.{u2}) [_inst_1 : AddGroup.{u1} G] [_inst_2 : AddTorsor.{u1, u2} G P _inst_1], Iff (Subsingleton.{succ u1} G) (Subsingleton.{succ u2} P)
but is expected to have type
  forall (G : Type.{u2}) (P : Type.{u1}) [_inst_1 : AddGroup.{u2} G] [_inst_2 : AddTorsor.{u2, u1} G P _inst_1], Iff (Subsingleton.{succ u2} G) (Subsingleton.{succ u1} P)
Case conversion may be inaccurate. Consider using '#align add_torsor.subsingleton_iff AddTorsor.subsingleton_iffₓ'. -/
theorem AddTorsor.subsingleton_iff (G P : Type _) [AddGroup G] [AddTorsor G P] :
    Subsingleton G ↔ Subsingleton P := by
  inhabit P
  exact (Equiv.vaddConst default).subsingleton_congr
#align add_torsor.subsingleton_iff AddTorsor.subsingleton_iff

