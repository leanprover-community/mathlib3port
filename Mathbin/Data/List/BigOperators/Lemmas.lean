/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Sébastien Gouëzel, Alex J. Best

! This file was ported from Lean 3 source module data.list.big_operators.lemmas
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.List.BigOperators.Basic
import Mathbin.Algebra.Group.Opposite
import Mathbin.Algebra.GroupPower.Basic
import Mathbin.Algebra.GroupWithZero.Commute
import Mathbin.Algebra.GroupWithZero.Divisibility
import Mathbin.Algebra.Order.WithZero
import Mathbin.Algebra.Ring.Basic
import Mathbin.Algebra.Ring.Divisibility
import Mathbin.Algebra.Ring.Commute
import Mathbin.Data.Int.Units
import Mathbin.Data.Set.Basic

/-! # Lemmas about `list.sum` and `list.prod` requiring extra algebra imports 

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.-/


open MulOpposite List

variable {ι α M N P M₀ G R : Type _}

namespace Commute

/- warning: commute.list_sum_right -> Commute.list_sum_right is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (a : R) (l : List.{u1} R), (forall (b : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) b l) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) a b)) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) a (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_1)) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (a : R) (l : List.{u1} R), (forall (b : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) b l) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) a b)) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) a (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align commute.list_sum_right Commute.list_sum_rightₓ'. -/
theorem list_sum_right [NonUnitalNonAssocSemiring R] (a : R) (l : List R)
    (h : ∀ b ∈ l, Commute a b) : Commute a l.Sum :=
  by
  induction' l with x xs ih
  · exact Commute.zero_right _
  · rw [List.sum_cons]
    exact (h _ <| mem_cons_self _ _).add_right (ih fun j hj => h _ <| mem_cons_of_mem _ hj)
#align commute.list_sum_right Commute.list_sum_right

/- warning: commute.list_sum_left -> Commute.list_sum_left is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (b : R) (l : List.{u1} R), (forall (a : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) a l) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) a b)) -> (Commute.{u1} R (Distrib.toHasMul.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_1)) l) b)
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : NonUnitalNonAssocSemiring.{u1} R] (b : R) (l : List.{u1} R), (forall (a : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) a l) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) a b)) -> (Commute.{u1} R (NonUnitalNonAssocSemiring.toMul.{u1} R _inst_1) (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R _inst_1)) (MulZeroClass.toZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R _inst_1)) l) b)
Case conversion may be inaccurate. Consider using '#align commute.list_sum_left Commute.list_sum_leftₓ'. -/
theorem list_sum_left [NonUnitalNonAssocSemiring R] (b : R) (l : List R)
    (h : ∀ a ∈ l, Commute a b) : Commute l.Sum b :=
  (Commute.list_sum_right _ _ fun x hx => (h _ hx).symm).symm
#align commute.list_sum_left Commute.list_sum_left

end Commute

namespace List

/- warning: list.pow_card_le_prod -> List.pow_card_le_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Preorder.{u1} M] [_inst_3 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2))] [_inst_4 : CovariantClass.{u1, u1} M M (HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)))) (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2))] (l : List.{u1} M) (n : M), (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) n x)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n (List.length.{u1} M l)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Preorder.{u1} M] [_inst_3 : CovariantClass.{u1, u1} M M (Function.swap.{succ u1, succ u1, succ u1} M M (fun (ᾰ : M) (ᾰ : M) => M) (fun (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.204 : M) (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.206 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.204 x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.206)) (fun (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.219 : M) (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.221 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.219 x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.221)] [_inst_4 : CovariantClass.{u1, u1} M M (fun (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.238 : M) (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.240 : M) => HMul.hMul.{u1, u1, u1} M M M (instHMul.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.238 x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.240) (fun (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.253 : M) (x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.255 : M) => LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.253 x._@.Mathlib.Data.List.BigOperators.Lemmas._hyg.255)] (l : List.{u1} M) (n : M), (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) n x)) -> (LE.le.{u1} M (Preorder.toLE.{u1} M _inst_2) (HPow.hPow.{u1, 0, u1} M Nat M (instHPow.{u1, 0} M Nat (Monoid.Pow.{u1} M _inst_1)) n (List.length.{u1} M l)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l))
Case conversion may be inaccurate. Consider using '#align list.pow_card_le_prod List.pow_card_le_prodₓ'. -/
@[to_additive card_nsmul_le_sum]
theorem pow_card_le_prod [Monoid M] [Preorder M]
    [CovariantClass M M (Function.swap (· * ·)) (· ≤ ·)] [CovariantClass M M (· * ·) (· ≤ ·)]
    (l : List M) (n : M) (h : ∀ x ∈ l, n ≤ x) : n ^ l.length ≤ l.Prod :=
  @prod_le_pow_card Mᵒᵈ _ _ _ _ l n h
#align list.pow_card_le_prod List.pow_card_le_prod
#align list.card_nsmul_le_sum List.card_nsmul_le_sum

/- warning: list.prod_eq_one_iff -> List.prod_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (l : List.{u1} M), Iff (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) l) (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))))))) (forall (x : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (OfNat.mk.{u1} M 1 (One.one.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))))))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CanonicallyOrderedMonoid.{u1} M] (l : List.{u1} M), Iff (Eq.{succ u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1)))) l) (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))))) (forall (x : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) x l) -> (Eq.{succ u1} M x (OfNat.ofNat.{u1} M 1 (One.toOfNat1.{u1} M (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M (OrderedCommMonoid.toCommMonoid.{u1} M (CanonicallyOrderedMonoid.toOrderedCommMonoid.{u1} M _inst_1))))))))
Case conversion may be inaccurate. Consider using '#align list.prod_eq_one_iff List.prod_eq_one_iffₓ'. -/
@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid M] (l : List M) :
    l.Prod = 1 ↔ ∀ x ∈ l, x = (1 : M) :=
  ⟨all_one_of_le_one_le_of_prod_eq_one fun _ _ => one_le _, fun h => by
    rw [eq_replicate.2 ⟨rfl, h⟩, prod_replicate, one_pow]⟩
#align list.prod_eq_one_iff List.prod_eq_one_iff
#align list.sum_eq_zero_iff List.sum_eq_zero_iff

#print List.neg_one_mem_of_prod_eq_neg_one /-
/-- If a product of integers is `-1`, then at least one factor must be `-1`. -/
theorem neg_one_mem_of_prod_eq_neg_one {l : List ℤ} (h : l.Prod = -1) : (-1 : ℤ) ∈ l :=
  by
  obtain ⟨x, h₁, h₂⟩ := exists_mem_ne_one_of_prod_ne_one (ne_of_eq_of_ne h (by decide))
  exact
    Or.resolve_left
        (int.is_unit_iff.mp
          (prod_is_unit_iff.mp (h.symm ▸ IsUnit.neg isUnit_one : IsUnit l.prod) x h₁))
        h₂ ▸
      h₁
#align list.neg_one_mem_of_prod_eq_neg_one List.neg_one_mem_of_prod_eq_neg_one
-/

#print List.length_le_sum_of_one_le /-
/-- If all elements in a list are bounded below by `1`, then the length of the list is bounded
by the sum of the elements. -/
theorem length_le_sum_of_one_le (L : List ℕ) (h : ∀ i ∈ L, 1 ≤ i) : L.length ≤ L.Sum :=
  by
  induction' L with j L IH h; · simp
  rw [sum_cons, length, add_comm]
  exact add_le_add (h _ (Set.mem_insert _ _)) (IH fun i hi => h i (Set.mem_union_right _ hi))
#align list.length_le_sum_of_one_le List.length_le_sum_of_one_le
-/

/- warning: list.dvd_prod -> List.dvd_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : M} {l : List.{u1} M}, (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a l) -> (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) a (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) l))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoid.{u1} M] {a : M} {l : List.{u1} M}, (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a l) -> (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (Monoid.toSemigroup.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) a (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1))) (Monoid.toOne.{u1} M (CommMonoid.toMonoid.{u1} M _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.dvd_prod List.dvd_prodₓ'. -/
theorem dvd_prod [CommMonoid M] {a} {l : List M} (ha : a ∈ l) : a ∣ l.Prod :=
  by
  let ⟨s, t, h⟩ := mem_split ha
  rw [h, prod_append, prod_cons, mul_left_comm]
  exact dvd_mul_right _ _
#align list.dvd_prod List.dvd_prod

/- warning: list.dvd_sum -> List.dvd_sum is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {a : R} {l : List.{u1} R}, (forall (x : R), (Membership.Mem.{u1, u1} R (List.{u1} R) (List.hasMem.{u1} R) x l) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) a x)) -> (Dvd.Dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) a (List.sum.{u1} R (Distrib.toHasAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) l))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : Semiring.{u1} R] {a : R} {l : List.{u1} R}, (forall (x : R), (Membership.mem.{u1, u1} R (List.{u1} R) (List.instMembershipList.{u1} R) x l) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) a x)) -> (Dvd.dvd.{u1} R (semigroupDvd.{u1} R (SemigroupWithZero.toSemigroup.{u1} R (NonUnitalSemiring.toSemigroupWithZero.{u1} R (Semiring.toNonUnitalSemiring.{u1} R _inst_1)))) a (List.sum.{u1} R (Distrib.toAdd.{u1} R (NonUnitalNonAssocSemiring.toDistrib.{u1} R (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} R (Semiring.toNonAssocSemiring.{u1} R _inst_1)))) (MonoidWithZero.toZero.{u1} R (Semiring.toMonoidWithZero.{u1} R _inst_1)) l))
Case conversion may be inaccurate. Consider using '#align list.dvd_sum List.dvd_sumₓ'. -/
theorem dvd_sum [Semiring R] {a} {l : List R} (h : ∀ x ∈ l, a ∣ x) : a ∣ l.Sum :=
  by
  induction' l with x l ih
  · exact dvd_zero _
  · rw [List.sum_cons]
    exact dvd_add (h _ (mem_cons_self _ _)) (ih fun x hx => h x (mem_cons_of_mem _ hx))
#align list.dvd_sum List.dvd_sum

section Alternating

variable [CommGroup α]

/- warning: list.alternating_prod_append -> List.alternatingProd_append is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (Append.append.{u1} (List.{u1} α) (List.hasAppend.{u1} α) l₁ l₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) l₁) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) l₂) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (List.length.{u1} α l₁))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (l₁ : List.{u1} α) (l₂ : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (HAppend.hAppend.{u1, u1, u1} (List.{u1} α) (List.{u1} α) (List.{u1} α) (instHAppend.{u1} (List.{u1} α) (List.instAppendList.{u1} α)) l₁ l₂)) (HMul.hMul.{u1, u1, u1} α α α (instHMul.{u1} α (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))))) (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) l₁) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) l₂) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (List.length.{u1} α l₁))))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_append List.alternatingProd_appendₓ'. -/
@[to_additive]
theorem alternatingProd_append :
    ∀ l₁ l₂ : List α,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternating_prod_cons, alternating_prod_append, length_cons, pow_succ,
      neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]
#align list.alternating_prod_append List.alternatingProd_append
#align list.alternating_sum_append List.alternatingSum_append

/- warning: list.alternating_prod_reverse -> List.alternatingProd_reverse is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) (List.reverse.{u1} α l)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) (List.alternatingProd.{u1} α (MulOneClass.toHasOne.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (MulOneClass.toHasMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (DivInvMonoid.toHasInv.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))) l) (HPow.hPow.{0, 0, 0} Int Nat Int (instHPow.{0, 0} Int Nat (Monoid.Pow.{0} Int Int.monoid)) (Neg.neg.{0} Int Int.hasNeg (OfNat.ofNat.{0} Int 1 (OfNat.mk.{0} Int 1 (One.one.{0} Int Int.hasOne)))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommGroup.{u1} α] (l : List.{u1} α), Eq.{succ u1} α (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (List.reverse.{u1} α l)) (HPow.hPow.{u1, 0, u1} α Int α (instHPow.{u1, 0} α Int (DivInvMonoid.Pow.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1)))) (List.alternatingProd.{u1} α (InvOneClass.toOne.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) (MulOneClass.toMul.{u1} α (Monoid.toMulOneClass.{u1} α (DivInvMonoid.toMonoid.{u1} α (Group.toDivInvMonoid.{u1} α (CommGroup.toGroup.{u1} α _inst_1))))) (InvOneClass.toInv.{u1} α (DivInvOneMonoid.toInvOneClass.{u1} α (DivisionMonoid.toDivInvOneMonoid.{u1} α (DivisionCommMonoid.toDivisionMonoid.{u1} α (CommGroup.toDivisionCommMonoid.{u1} α _inst_1))))) l) (HPow.hPow.{0, 0, 0} Int Nat Int Int.instHPowIntNat (Neg.neg.{0} Int Int.instNegInt (OfNat.ofNat.{0} Int 1 (instOfNatInt 1))) (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) (List.length.{u1} α l) (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))
Case conversion may be inaccurate. Consider using '#align list.alternating_prod_reverse List.alternatingProd_reverseₓ'. -/
@[to_additive]
theorem alternatingProd_reverse :
    ∀ l : List α, alternatingProd (reverse l) = alternatingProd l ^ (-1 : ℤ) ^ (length l + 1)
  | [] => by simp only [alternating_prod_nil, one_zpow, reverse_nil]
  | a :: l =>
    by
    simp_rw [reverse_cons, alternating_prod_append, alternating_prod_reverse,
      alternating_prod_singleton, alternating_prod_cons, length_reverse, length, pow_succ, neg_mul,
      one_mul, zpow_neg, inv_inv]
    rw [mul_comm, ← div_eq_mul_inv, div_zpow]
#align list.alternating_prod_reverse List.alternatingProd_reverse
#align list.alternating_sum_reverse List.alternatingSum_reverse

end Alternating

/- warning: list.sum_map_mul_left -> List.sum_map_mul_left is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] (L : List.{u1} ι) (f : ι -> R) (r : R), Eq.{succ u2} R (List.sum.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R (fun (b : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) r (f b)) L)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) r (List.sum.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R f L)))
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] (L : List.{u1} ι) (f : ι -> R) (r : R), Eq.{succ u2} R (List.sum.{u2} R (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R (fun (b : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) r (f b)) L)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) r (List.sum.{u2} R (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R f L)))
Case conversion may be inaccurate. Consider using '#align list.sum_map_mul_left List.sum_map_mul_leftₓ'. -/
theorem sum_map_mul_left [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => r * f b).Sum = r * (L.map f).Sum :=
  sum_map_hom L f <| AddMonoidHom.mulLeft r
#align list.sum_map_mul_left List.sum_map_mul_left

/- warning: list.sum_map_mul_right -> List.sum_map_mul_right is a dubious translation:
lean 3 declaration is
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] (L : List.{u1} ι) (f : ι -> R) (r : R), Eq.{succ u2} R (List.sum.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R (fun (b : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) (f b) r) L)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (Distrib.toHasMul.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1))) (List.sum.{u2} R (Distrib.toHasAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toHasZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R f L)) r)
but is expected to have type
  forall {ι : Type.{u1}} {R : Type.{u2}} [_inst_1 : NonUnitalNonAssocSemiring.{u2} R] (L : List.{u1} ι) (f : ι -> R) (r : R), Eq.{succ u2} R (List.sum.{u2} R (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R (fun (b : ι) => HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) (f b) r) L)) (HMul.hMul.{u2, u2, u2} R R R (instHMul.{u2} R (NonUnitalNonAssocSemiring.toMul.{u2} R _inst_1)) (List.sum.{u2} R (Distrib.toAdd.{u2} R (NonUnitalNonAssocSemiring.toDistrib.{u2} R _inst_1)) (MulZeroClass.toZero.{u2} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} R _inst_1)) (List.map.{u1, u2} ι R f L)) r)
Case conversion may be inaccurate. Consider using '#align list.sum_map_mul_right List.sum_map_mul_rightₓ'. -/
theorem sum_map_mul_right [NonUnitalNonAssocSemiring R] (L : List ι) (f : ι → R) (r : R) :
    (L.map fun b => f b * r).Sum = (L.map f).Sum * r :=
  sum_map_hom L f <| AddMonoidHom.mulRight r
#align list.sum_map_mul_right List.sum_map_mul_right

end List

namespace MulOpposite

open List

variable [Monoid M]

/- warning: mul_opposite.op_list_prod -> MulOpposite.op_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M), Eq.{succ u1} (MulOpposite.{u1} M) (MulOpposite.op.{u1} M (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l)) (List.prod.{u1} (MulOpposite.{u1} M) (MulOpposite.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (MulOpposite.hasOne.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (List.reverse.{u1} (MulOpposite.{u1} M) (List.map.{u1, u1} M (MulOpposite.{u1} M) (MulOpposite.op.{u1} M) l)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} M), Eq.{succ u1} (MulOpposite.{u1} M) (MulOpposite.op.{u1} M (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) l)) (List.prod.{u1} (MulOpposite.{u1} M) (MulOpposite.instMulMulOpposite.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (MulOpposite.instOneMulOpposite.{u1} M (Monoid.toOne.{u1} M _inst_1)) (List.reverse.{u1} (MulOpposite.{u1} M) (List.map.{u1, u1} M (MulOpposite.{u1} M) (MulOpposite.op.{u1} M) l)))
Case conversion may be inaccurate. Consider using '#align mul_opposite.op_list_prod MulOpposite.op_list_prodₓ'. -/
theorem op_list_prod : ∀ l : List M, op l.Prod = (l.map op).reverse.Prod
  | [] => rfl
  | x :: xs => by
    rw [List.prod_cons, List.map_cons, List.reverse_cons', List.prod_concat, op_mul, op_list_prod]
#align mul_opposite.op_list_prod MulOpposite.op_list_prod

/- warning: mul_opposite.unop_list_prod -> MulOpposite.unop_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} (MulOpposite.{u1} M)), Eq.{succ u1} M (MulOpposite.unop.{u1} M (List.prod.{u1} (MulOpposite.{u1} M) (MulOpposite.hasMul.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (MulOpposite.hasOne.{u1} M (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) l)) (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (List.reverse.{u1} M (List.map.{u1, u1} (MulOpposite.{u1} M) M (MulOpposite.unop.{u1} M) l)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : Monoid.{u1} M] (l : List.{u1} (MulOpposite.{u1} M)), Eq.{succ u1} M (MulOpposite.unop.{u1} M (List.prod.{u1} (MulOpposite.{u1} M) (MulOpposite.instMulMulOpposite.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1))) (MulOpposite.instOneMulOpposite.{u1} M (Monoid.toOne.{u1} M _inst_1)) l)) (List.prod.{u1} M (MulOneClass.toMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (Monoid.toOne.{u1} M _inst_1) (List.reverse.{u1} M (List.map.{u1, u1} (MulOpposite.{u1} M) M (MulOpposite.unop.{u1} M) l)))
Case conversion may be inaccurate. Consider using '#align mul_opposite.unop_list_prod MulOpposite.unop_list_prodₓ'. -/
theorem MulOpposite.unop_list_prod (l : List Mᵐᵒᵖ) : l.Prod.unop = (l.map unop).reverse.Prod := by
  rw [← op_inj, op_unop, MulOpposite.op_list_prod, map_reverse, map_map, reverse_reverse,
    op_comp_unop, map_id]
#align mul_opposite.unop_list_prod MulOpposite.unop_list_prod

end MulOpposite

section MonoidHom

variable [Monoid M] [Monoid N]

/- warning: unop_map_list_prod -> unop_map_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u1, u2} F M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))] (f : F) (l : List.{u1} M), Eq.{succ u2} N (MulOpposite.unop.{u2} N (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> (MulOpposite.{u2} N)) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => MulOpposite.{u2} N) (MulHomClass.toFunLike.{u3, u1, u2} F M (MulOpposite.{u2} N) (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (MulOpposite.{u2} N) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) _inst_3))) f (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))) (List.prod.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (List.reverse.{u2} N (List.map.{u1, u2} M N (Function.comp.{succ u1, succ u2, succ u2} M (MulOpposite.{u2} N) N (MulOpposite.unop.{u2} N) (coeFn.{succ u3, max (succ u1) (succ u2)} F (fun (_x : F) => M -> (MulOpposite.{u2} N)) (FunLike.hasCoeToFun.{succ u3, succ u1, succ u2} F M (fun (_x : M) => MulOpposite.{u2} N) (MulHomClass.toFunLike.{u3, u1, u2} F M (MulOpposite.{u2} N) (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasMul.{u2} (MulOpposite.{u2} N) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u1, u2} F M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) _inst_3))) f)) l)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] {F : Type.{u3}} [_inst_3 : MonoidHomClass.{u3, u2, u1} F M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))] (f : F) (l : List.{u2} M), Eq.{succ u1} N (MulOpposite.unop.{u1} N (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => MulOpposite.{u1} N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M (MulOpposite.{u1} N) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (MulOpposite.{u1} N) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) _inst_3)) f (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l))) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.reverse.{u1} N (List.map.{u2, u1} M N (Function.comp.{succ u2, succ u1, succ u1} M (MulOpposite.{u1} N) N (MulOpposite.unop.{u1} N) (FunLike.coe.{succ u3, succ u2, succ u1} F M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => MulOpposite.{u1} N) _x) (MulHomClass.toFunLike.{u3, u2, u1} F M (MulOpposite.{u1} N) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (MulOpposite.{u1} N) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{u3, u2, u1} F M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) _inst_3)) f)) l)))
Case conversion may be inaccurate. Consider using '#align unop_map_list_prod unop_map_list_prodₓ'. -/
/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements. -/
theorem unop_map_list_prod {F : Type _} [MonoidHomClass F M Nᵐᵒᵖ] (f : F) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod := by
  rw [map_list_prod f l, MulOpposite.unop_list_prod, List.map_map]
#align unop_map_list_prod unop_map_list_prod

namespace MonoidHom

/- warning: monoid_hom.unop_map_list_prod -> MonoidHom.unop_map_list_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} {N : Type.{u2}} [_inst_1 : Monoid.{u1} M] [_inst_2 : Monoid.{u2} N] (f : MonoidHom.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (l : List.{u1} M), Eq.{succ u2} N (MulOpposite.unop.{u2} N (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) => M -> (MulOpposite.{u2} N)) (MonoidHom.hasCoeToFun.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) f (List.prod.{u1} M (MulOneClass.toHasMul.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) (MulOneClass.toHasOne.{u1} M (Monoid.toMulOneClass.{u1} M _inst_1)) l))) (List.prod.{u2} N (MulOneClass.toHasMul.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (MulOneClass.toHasOne.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2)) (List.reverse.{u2} N (List.map.{u1, u2} M N (Function.comp.{succ u1, succ u2, succ u2} M (MulOpposite.{u2} N) N (MulOpposite.unop.{u2} N) (coeFn.{max (succ u2) (succ u1), max (succ u1) (succ u2)} (MonoidHom.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) (fun (_x : MonoidHom.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) => M -> (MulOpposite.{u2} N)) (MonoidHom.hasCoeToFun.{u1, u2} M (MulOpposite.{u2} N) (Monoid.toMulOneClass.{u1} M _inst_1) (MulOpposite.mulOneClass.{u2} N (Monoid.toMulOneClass.{u2} N _inst_2))) f)) l)))
but is expected to have type
  forall {M : Type.{u2}} {N : Type.{u1}} [_inst_1 : Monoid.{u2} M] [_inst_2 : Monoid.{u1} N] (f : MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (l : List.{u2} M), Eq.{succ u1} N (MulOpposite.unop.{u1} N (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => MulOpposite.{u1} N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (MulOpposite.{u1} N) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (MulOpposite.{u1} N) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))))) f (List.prod.{u2} M (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (Monoid.toOne.{u2} M _inst_1) l))) (List.prod.{u1} N (MulOneClass.toMul.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (Monoid.toOne.{u1} N _inst_2) (List.reverse.{u1} N (List.map.{u2, u1} M N (Function.comp.{succ u2, succ u1, succ u1} M (MulOpposite.{u1} N) N (MulOpposite.unop.{u1} N) (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (fun (_x : M) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2398 : M) => MulOpposite.{u1} N) _x) (MulHomClass.toFunLike.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (MulOpposite.{u1} N) (MulOneClass.toMul.{u2} M (Monoid.toMulOneClass.{u2} M _inst_1)) (MulOneClass.toMul.{u1} (MulOpposite.{u1} N) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) (MonoidHomClass.toMulHomClass.{max u2 u1, u2, u1} (MonoidHom.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))) M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2)) (MonoidHom.monoidHomClass.{u2, u1} M (MulOpposite.{u1} N) (Monoid.toMulOneClass.{u2} M _inst_1) (MulOpposite.instMulOneClassMulOpposite.{u1} N (Monoid.toMulOneClass.{u1} N _inst_2))))) f)) l)))
Case conversion may be inaccurate. Consider using '#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prodₓ'. -/
/-- A morphism into the opposite monoid acts on the product by acting on the reversed elements.

Deprecated, use `_root_.unop_map_list_prod` instead. -/
protected theorem unop_map_list_prod (f : M →* Nᵐᵒᵖ) (l : List M) :
    (f l.Prod).unop = (l.map (MulOpposite.unop ∘ f)).reverse.Prod :=
  unop_map_list_prod f l
#align monoid_hom.unop_map_list_prod MonoidHom.unop_map_list_prod

end MonoidHom

end MonoidHom

