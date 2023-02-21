/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Bhavik Mehta, Eric Wieser

! This file was ported from Lean 3 source module algebra.big_operators.multiset.lemmas
! leanprover-community/mathlib commit f2f413b9d4be3a02840d0663dace76e8fe3da053
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Lemmas
import Mathbin.Algebra.BigOperators.Multiset.Basic

/-! # Lemmas about `multiset.sum` and `multiset.prod` requiring extra algebra imports 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


variable {ι α β γ : Type _}

namespace Multiset

#print Multiset.dvd_prod /-
theorem dvd_prod [CommMonoid α] {s : Multiset α} {a : α} : a ∈ s → a ∣ s.Prod :=
  Quotient.inductionOn s (fun l a h => by simpa using List.dvd_prod h) a
#align multiset.dvd_prod Multiset.dvd_prod
-/

/- warning: multiset.prod_eq_one_iff -> Multiset.prod_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {m : Multiset.{u1} α}, Iff (Eq.{succ u1} α (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)) m) (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))) (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x m) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (OfNat.mk.{u1} α 1 (One.one.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} α] {m : Multiset.{u1} α}, Iff (Eq.{succ u1} α (Multiset.prod.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1)) m) (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))) (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x m) -> (Eq.{succ u1} α x (OfNat.ofNat.{u1} α 1 (One.toOfNat1.{u1} α (Monoid.toOne.{u1} α (CommMonoid.toMonoid.{u1} α (OrderedCommMonoid.toCommMonoid.{u1} α (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} α _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_eq_one_iff Multiset.prod_eq_one_iffₓ'. -/
@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid α] {m : Multiset α} :
    m.Prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
  Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff l
#align multiset.prod_eq_one_iff Multiset.prod_eq_one_iff
#align multiset.sum_eq_zero_iff Multiset.sum_eq_zero_iff

end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

/- warning: commute.multiset_sum_right -> Commute.multiset_sum_right is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] (s : Multiset.{u1} α) (a : α), (forall (b : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) b s) -> (Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) a b)) -> (Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) a (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) s))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] (s : Multiset.{u1} α) (a : α), (forall (b : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) b s) -> (Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1) a b)) -> (Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1) a (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) s))
Case conversion may be inaccurate. Consider using '#align commute.multiset_sum_right Commute.multiset_sum_rightₓ'. -/
theorem multiset_sum_right (s : Multiset α) (a : α) (h : ∀ b ∈ s, Commute a b) : Commute a s.Sum :=
  by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, coe_sum]
  exact Commute.list_sum_right _ _ h
#align commute.multiset_sum_right Commute.multiset_sum_right

/- warning: commute.multiset_sum_left -> Commute.multiset_sum_left is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] (s : Multiset.{u1} α) (b : α), (forall (a : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) -> (Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) a b)) -> (Commute.{u1} α (Distrib.toHasMul.{u1} α (NonUnitalNonAssocSemiring.toDistrib.{u1} α _inst_1)) (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) s) b)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} α] (s : Multiset.{u1} α) (b : α), (forall (a : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) -> (Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1) a b)) -> (Commute.{u1} α (NonUnitalNonAssocSemiring.toMul.{u1} α _inst_1) (Multiset.sum.{u1} α (NonUnitalNonAssocSemiring.toAddCommMonoid.{u1} α _inst_1) s) b)
Case conversion may be inaccurate. Consider using '#align commute.multiset_sum_left Commute.multiset_sum_leftₓ'. -/
theorem multiset_sum_left (s : Multiset α) (b : α) (h : ∀ a ∈ s, Commute a b) : Commute s.Sum b :=
  (Commute.multiset_sum_right _ _ fun a ha => (h _ ha).symm).symm
#align commute.multiset_sum_left Commute.multiset_sum_left

end Commute

