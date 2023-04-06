/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland

! This file was ported from Lean 3 source module algebra.ring.divisibility
! leanprover-community/mathlib commit e8638a0fcaf73e4500469f368ef9494e495099b3
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Divisibility.Basic
import Mathbin.Algebra.Hom.Equiv.Basic
import Mathbin.Algebra.Ring.Defs

/-!
# Lemmas about divisibility in rings

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α β : Type _}

section DistribSemigroup

variable [Add α] [Semigroup α]

/- warning: dvd_add -> dvd_add is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Semigroup.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (Semigroup.toHasMul.{u1} α _inst_2) _inst_1] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a c) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Add.{u1} α] [_inst_2 : Semigroup.{u1} α] [_inst_3 : LeftDistribClass.{u1} α (Semigroup.toMul.{u1} α _inst_2) _inst_1] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a c) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_2) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α _inst_1) b c))
Case conversion may be inaccurate. Consider using '#align dvd_add dvd_addₓ'. -/
theorem dvd_add [LeftDistribClass α] {a b c : α} (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b + c :=
  Dvd.elim h₁ fun d hd => Dvd.elim h₂ fun e he => Dvd.intro (d + e) (by simp [left_distrib, hd, he])
#align dvd_add dvd_add

alias dvd_add ← Dvd.Dvd.add
#align has_dvd.dvd.add Dvd.Dvd.add

end DistribSemigroup

/- warning: two_dvd_bit0 -> two_dvd_bit0 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddCommMonoidWithOne.toAddMonoidWithOne.{u1} α (NonAssocSemiring.toAddCommMonoidWithOne.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))))))) (bit0.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semiring.{u1} α] {a : α}, Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (Semiring.toNonUnitalSemiring.{u1} α _inst_1)))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (Semiring.toNatCast.{u1} α _inst_1) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (bit0.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} α (Semiring.toNonAssocSemiring.{u1} α _inst_1)))) a)
Case conversion may be inaccurate. Consider using '#align two_dvd_bit0 two_dvd_bit0ₓ'. -/
@[simp]
theorem two_dvd_bit0 [Semiring α] {a : α} : 2 ∣ bit0 a :=
  ⟨a, bit0_eq_two_mul _⟩
#align two_dvd_bit0 two_dvd_bit0

section NonUnitalCommSemiring

variable [NonUnitalCommSemiring α] [NonUnitalCommSemiring β] {a b c : α}

/- warning: has_dvd.dvd.linear_comb -> Dvd.dvd.linear_comb is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] {d : α} {x : α} {y : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d x) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d y) -> (forall (a : α) (b : α), Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))))) b y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommSemiring.{u1} α] {d : α} {x : α} {y : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d x) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d y) -> (forall (a : α) (b : α), Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) d (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α (NonUnitalSemiring.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalCommSemiring.toNonUnitalSemiring.{u1} α _inst_1)))) b y)))
Case conversion may be inaccurate. Consider using '#align has_dvd.dvd.linear_comb Dvd.dvd.linear_combₓ'. -/
theorem Dvd.dvd.linear_comb {d x y : α} (hdx : d ∣ x) (hdy : d ∣ y) (a b : α) : d ∣ a * x + b * y :=
  dvd_add (hdx.mul_left a) (hdy.mul_left b)
#align has_dvd.dvd.linear_comb Dvd.dvd.linear_comb

end NonUnitalCommSemiring

section Semigroup

variable [Semigroup α] [HasDistribNeg α] {a b c : α}

/- warning: dvd_neg -> dvd_neg is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (Semigroup.toHasMul.{u1} α _inst_1) _inst_2)) b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (Semigroup.toMul.{u1} α _inst_1)] (a : α) (b : α), Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (Semigroup.toMul.{u1} α _inst_1) _inst_2)) b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align dvd_neg dvd_negₓ'. -/
/-- An element `a` of a semigroup with a distributive negation divides the negation of an element
`b` iff `a` divides `b`. -/
@[simp]
theorem dvd_neg : a ∣ -b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by simpa
#align dvd_neg dvd_neg

/- warning: neg_dvd -> neg_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (Semigroup.toHasMul.{u1} α _inst_1)] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toHasNeg.{u1} α (HasDistribNeg.toHasInvolutiveNeg.{u1} α (Semigroup.toHasMul.{u1} α _inst_1) _inst_2)) a) b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Semigroup.{u1} α] [_inst_2 : HasDistribNeg.{u1} α (Semigroup.toMul.{u1} α _inst_1)] (a : α) (b : α), Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) (Neg.neg.{u1} α (InvolutiveNeg.toNeg.{u1} α (HasDistribNeg.toInvolutiveNeg.{u1} α (Semigroup.toMul.{u1} α _inst_1) _inst_2)) a) b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α _inst_1) a b)
Case conversion may be inaccurate. Consider using '#align neg_dvd neg_dvdₓ'. -/
/-- The negation of an element `a` of a semigroup with a distributive negation divides another
element `b` iff `a` divides `b`. -/
@[simp]
theorem neg_dvd : -a ∣ b ↔ a ∣ b :=
  (Equiv.neg _).exists_congr_left.trans <| by simpa
#align neg_dvd neg_dvd

alias neg_dvd ↔ Dvd.Dvd.of_neg_left Dvd.Dvd.neg_left
#align has_dvd.dvd.of_neg_left Dvd.Dvd.of_neg_left
#align has_dvd.dvd.neg_left Dvd.Dvd.neg_left

alias dvd_neg ↔ Dvd.Dvd.of_neg_right Dvd.Dvd.neg_right
#align has_dvd.dvd.of_neg_right Dvd.Dvd.of_neg_right
#align has_dvd.dvd.neg_right Dvd.Dvd.neg_right

end Semigroup

section NonUnitalRing

variable [NonUnitalRing α] {a b c : α}

/- warning: dvd_sub -> dvd_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c))
Case conversion may be inaccurate. Consider using '#align dvd_sub dvd_subₓ'. -/
theorem dvd_sub (h₁ : a ∣ b) (h₂ : a ∣ c) : a ∣ b - c := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_right
#align dvd_sub dvd_sub

alias dvd_sub ← Dvd.Dvd.sub
#align has_dvd.dvd.sub Dvd.Dvd.sub

/- warning: dvd_add_left -> dvd_add_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) b c)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) b c)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b))
Case conversion may be inaccurate. Consider using '#align dvd_add_left dvd_add_leftₓ'. -/
/-- If an element `a` divides another element `c` in a ring, `a` divides the sum of another element
`b` with `c` iff `a` divides `b`. -/
theorem dvd_add_left (h : a ∣ c) : a ∣ b + c ↔ a ∣ b :=
  ⟨fun H => by simpa only [add_sub_cancel] using dvd_sub H h, fun h₂ => dvd_add h₂ h⟩
#align dvd_add_left dvd_add_left

/- warning: dvd_add_right -> dvd_add_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) b c)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1))))) b c)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align dvd_add_right dvd_add_rightₓ'. -/
/-- If an element `a` divides another element `b` in a ring, `a` divides the sum of `b` and another
element `c` iff `a` divides `c`. -/
theorem dvd_add_right (h : a ∣ b) : a ∣ b + c ↔ a ∣ c := by rw [add_comm] <;> exact dvd_add_left h
#align dvd_add_right dvd_add_right

/-- If an element `a` divides another element `c` in a ring, `a` divides the difference of another
element `b` with `c` iff `a` divides `b`. -/
theorem dvd_sub_left (h : a ∣ c) : a ∣ b - c ↔ a ∣ b := by
  simpa only [← sub_eq_add_neg] using dvd_add_left (dvd_neg.2 h)
#align dvd_sub_left dvd_sub_left

/-- If an element `a` divides another element `b` in a ring, `a` divides the difference of `b` and
another element `c` iff `a` divides `c`. -/
theorem dvd_sub_right (h : a ∣ b) : a ∣ b - c ↔ a ∣ c := by
  rw [sub_eq_add_neg, dvd_add_right h, dvd_neg]
#align dvd_sub_right dvd_sub_right

/- warning: dvd_iff_dvd_of_dvd_sub -> dvd_iff_dvd_of_dvd_sub is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c)) -> (Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c)) -> (Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a b) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a c))
Case conversion may be inaccurate. Consider using '#align dvd_iff_dvd_of_dvd_sub dvd_iff_dvd_of_dvd_subₓ'. -/
theorem dvd_iff_dvd_of_dvd_sub (h : a ∣ b - c) : a ∣ b ↔ a ∣ c := by
  rw [← sub_add_cancel b c, dvd_add_right h]
#align dvd_iff_dvd_of_dvd_sub dvd_iff_dvd_of_dvd_sub

/- warning: dvd_sub_comm -> dvd_sub_comm is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) c b))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalRing.{u1} α] {a : α} {b : α} {c : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) b c)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α _inst_1)))) a (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α _inst_1)))))) c b))
Case conversion may be inaccurate. Consider using '#align dvd_sub_comm dvd_sub_commₓ'. -/
theorem dvd_sub_comm : a ∣ b - c ↔ a ∣ c - b := by rw [← dvd_neg, neg_sub]
#align dvd_sub_comm dvd_sub_comm

end NonUnitalRing

section Ring

variable [Ring α] {a b c : α}

/- warning: two_dvd_bit1 -> two_dvd_bit1 is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))))) (bit1.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))) (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) a)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (OfNat.mk.{u1} α 2 (bit0.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1)) (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1)))))))) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (AddMonoidWithOne.toOne.{u1} α (AddGroupWithOne.toAddMonoidWithOne.{u1} α (AddCommGroupWithOne.toAddGroupWithOne.{u1} α (Ring.toAddCommGroupWithOne.{u1} α _inst_1))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (bit1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1))))) a)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) (OfNat.ofNat.{u1} α 2 (instOfNat.{u1} α 2 (NonAssocRing.toNatCast.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (NonAssocRing.toOne.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align two_dvd_bit1 two_dvd_bit1ₓ'. -/
theorem two_dvd_bit1 : 2 ∣ bit1 a ↔ (2 : α) ∣ 1 :=
  dvd_add_right two_dvd_bit0
#align two_dvd_bit1 two_dvd_bit1

/- warning: dvd_add_self_left -> dvd_add_self_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) a b)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) a b)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align dvd_add_self_left dvd_add_self_leftₓ'. -/
/-- An element a divides the sum a + b if and only if a divides b.-/
@[simp]
theorem dvd_add_self_left {a b : α} : a ∣ a + b ↔ a ∣ b :=
  dvd_add_right (dvd_refl a)
#align dvd_add_self_left dvd_add_self_left

/- warning: dvd_add_self_right -> dvd_add_self_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, Iff (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toHasAdd.{u1} α (Ring.toDistrib.{u1} α _inst_1))) b a)) (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Ring.{u1} α] {a : α} {b : α}, Iff (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a (HAdd.hAdd.{u1, u1, u1} α α α (instHAdd.{u1} α (Distrib.toAdd.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonAssocRing.toNonUnitalNonAssocRing.{u1} α (Ring.toNonAssocRing.{u1} α _inst_1)))))) b a)) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (Ring.toNonUnitalRing.{u1} α _inst_1))))) a b)
Case conversion may be inaccurate. Consider using '#align dvd_add_self_right dvd_add_self_rightₓ'. -/
/-- An element a divides the sum b + a if and only if a divides b.-/
@[simp]
theorem dvd_add_self_right {a b : α} : a ∣ b + a ↔ a ∣ b :=
  dvd_add_left (dvd_refl a)
#align dvd_add_self_right dvd_add_self_right

/-- An element `a` divides the difference `a - b` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_left : a ∣ a - b ↔ a ∣ b :=
  dvd_sub_right dvd_rfl
#align dvd_sub_self_left dvd_sub_self_left

/-- An element `a` divides the difference `b - a` if and only if `a` divides `b`. -/
@[simp]
theorem dvd_sub_self_right : a ∣ b - a ↔ a ∣ b :=
  dvd_sub_left dvd_rfl
#align dvd_sub_self_right dvd_sub_self_right

end Ring

section NonUnitalCommRing

variable [NonUnitalCommRing α] {a b c : α}

/- warning: dvd_mul_sub_mul -> dvd_mul_sub_mul is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommRing.{u1} α] {k : α} {a : α} {b : α} {x : α} {y : α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) a b)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) x y)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toHasSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))))) b y)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalCommRing.{u1} α] {k : α} {a : α} {b : α} {x : α} {y : α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) a b)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) x y)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (NonUnitalSemiring.toSemigroupWithZero.{u1} α (NonUnitalRing.toNonUnitalSemiring.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))) k (HSub.hSub.{u1, u1, u1} α α α (instHSub.{u1} α (SubNegMonoid.toSub.{u1} α (AddGroup.toSubNegMonoid.{u1} α (AddCommGroup.toAddGroup.{u1} α (NonUnitalNonAssocRing.toAddCommGroup.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1))))))) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) a x) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (NonUnitalNonAssocRing.toMul.{u1} α (NonUnitalRing.toNonUnitalNonAssocRing.{u1} α (NonUnitalCommRing.toNonUnitalRing.{u1} α _inst_1)))) b y)))
Case conversion may be inaccurate. Consider using '#align dvd_mul_sub_mul dvd_mul_sub_mulₓ'. -/
theorem dvd_mul_sub_mul {k a b x y : α} (hab : k ∣ a - b) (hxy : k ∣ x - y) : k ∣ a * x - b * y :=
  by
  convert dvd_add (hxy.mul_left a) (hab.mul_right y)
  rw [mul_sub_left_distrib, mul_sub_right_distrib]
  simp only [sub_eq_add_neg, add_assoc, neg_add_cancel_left]
#align dvd_mul_sub_mul dvd_mul_sub_mul

end NonUnitalCommRing

