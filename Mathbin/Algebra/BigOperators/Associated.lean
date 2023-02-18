/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen

! This file was ported from Lean 3 source module algebra.big_operators.associated
! leanprover-community/mathlib commit 2738d2ca56cbc63be80c3bd48e9ed90ad94e947d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.BigOperators.Finsupp

/-!
# Products of associated, prime, and irreducible elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some theorems relating definitions in `algebra.associated`
and products of multisets, finsets, and finsupps.

-/


variable {α β γ δ : Type _}

-- mathport name: «expr ~ᵤ »
-- the same local notation used in `algebra.associated`
local infixl:50 " ~ᵤ " => Associated

open BigOperators

namespace Prime

variable [CommMonoidWithZero α] {p : α} (hp : Prime p)

/- warning: prime.exists_mem_multiset_dvd -> Prime.exists_mem_multiset_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Multiset.{u1} α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s)) -> (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) a s) => Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p a))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Multiset.{u1} α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s)) -> (Exists.{succ u1} α (fun (a : α) => And (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) a s) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p a))))
Case conversion may be inaccurate. Consider using '#align prime.exists_mem_multiset_dvd Prime.exists_mem_multiset_dvdₓ'. -/
theorem exists_mem_multiset_dvd {s : Multiset α} : p ∣ s.Prod → ∃ a ∈ s, p ∣ a :=
  Multiset.induction_on s (fun h => (hp.not_dvd_one h).elim) fun a s ih h =>
    have : p ∣ a * s.Prod := by simpa using h
    match hp.dvd_or_dvd this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align prime.exists_mem_multiset_dvd Prime.exists_mem_multiset_dvd

include hp

/- warning: prime.exists_mem_multiset_map_dvd -> Prime.exists_mem_multiset_map_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Multiset.{u2} β} {f : β -> α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} β α f s))) -> (Exists.{succ u2} β (fun (a : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) a s) (fun (H : Membership.Mem.{u2, u2} β (Multiset.{u2} β) (Multiset.hasMem.{u2} β) a s) => Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (f a)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Multiset.{u2} β} {f : β -> α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) (Multiset.map.{u2, u1} β α f s))) -> (Exists.{succ u2} β (fun (a : β) => And (Membership.mem.{u2, u2} β (Multiset.{u2} β) (Multiset.instMembershipMultiset.{u2} β) a s) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (f a)))))
Case conversion may be inaccurate. Consider using '#align prime.exists_mem_multiset_map_dvd Prime.exists_mem_multiset_map_dvdₓ'. -/
theorem exists_mem_multiset_map_dvd {s : Multiset β} {f : β → α} :
    p ∣ (s.map f).Prod → ∃ a ∈ s, p ∣ f a := fun h => by
  simpa only [exists_prop, Multiset.mem_map, exists_exists_and_eq_and] using
    hp.exists_mem_multiset_dvd h
#align prime.exists_mem_multiset_map_dvd Prime.exists_mem_multiset_map_dvd

/- warning: prime.exists_mem_finset_dvd -> Prime.exists_mem_finset_dvd is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Finset.{u2} β} {f : β -> α}, (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Finset.prod.{u1, u2} α β (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s f)) -> (Exists.{succ u2} β (fun (i : β) => Exists.{0} (Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) i s) (fun (H : Membership.Mem.{u2, u2} β (Finset.{u2} β) (Finset.hasMem.{u2} β) i s) => Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (f i)))))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α _inst_1 p) -> (forall {s : Finset.{u2} β} {f : β -> α}, (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (Finset.prod.{u1, u2} α β (CommMonoidWithZero.toCommMonoid.{u1} α _inst_1) s f)) -> (Exists.{succ u2} β (fun (i : β) => And (Membership.mem.{u2, u2} β (Finset.{u2} β) (Finset.instMembershipFinset.{u2} β) i s) (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α _inst_1)))) p (f i)))))
Case conversion may be inaccurate. Consider using '#align prime.exists_mem_finset_dvd Prime.exists_mem_finset_dvdₓ'. -/
theorem exists_mem_finset_dvd {s : Finset β} {f : β → α} : p ∣ s.Prod f → ∃ i ∈ s, p ∣ f i :=
  hp.exists_mem_multiset_map_dvd
#align prime.exists_mem_finset_dvd Prime.exists_mem_finset_dvd

end Prime

/- warning: exists_associated_mem_of_dvd_prod -> exists_associated_mem_of_dvd_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {s : Multiset.{u1} α}, (forall (r : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) r s) -> (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) r)) -> (Dvd.Dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (q : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) q s) (fun (H : Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) q s) => Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p q))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {p : α}, (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) p) -> (forall {s : Multiset.{u1} α}, (forall (r : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) r s) -> (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) r)) -> (Dvd.dvd.{u1} α (semigroupDvd.{u1} α (SemigroupWithZero.toSemigroup.{u1} α (MonoidWithZero.toSemigroupWithZero.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) p (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) s)) -> (Exists.{succ u1} α (fun (q : α) => And (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) q s) (Associated.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) p q))))
Case conversion may be inaccurate. Consider using '#align exists_associated_mem_of_dvd_prod exists_associated_mem_of_dvd_prodₓ'. -/
theorem exists_associated_mem_of_dvd_prod [CancelCommMonoidWithZero α] {p : α} (hp : Prime p)
    {s : Multiset α} : (∀ r ∈ s, Prime r) → p ∣ s.Prod → ∃ q ∈ s, p ~ᵤ q :=
  Multiset.induction_on s (by simp [mt isUnit_iff_dvd_one.2 hp.not_unit]) fun a s ih hs hps =>
    by
    rw [Multiset.prod_cons] at hps
    cases' hp.dvd_or_dvd hps with h h
    · have hap := hs a (Multiset.mem_cons.2 (Or.inl rfl))
      exact ⟨a, Multiset.mem_cons_self a _, hp.associated_of_dvd hap h⟩
    · rcases ih (fun r hr => hs _ (Multiset.mem_cons.2 (Or.inr hr))) h with ⟨q, hq₁, hq₂⟩
      exact ⟨q, Multiset.mem_cons.2 (Or.inr hq₁), hq₂⟩
#align exists_associated_mem_of_dvd_prod exists_associated_mem_of_dvd_prod

#print Multiset.prod_primes_dvd /-
theorem Multiset.prod_primes_dvd [CancelCommMonoidWithZero α]
    [∀ a : α, DecidablePred (Associated a)] {s : Multiset α} (n : α) (h : ∀ a ∈ s, Prime a)
    (div : ∀ a ∈ s, a ∣ n) (uniq : ∀ a, s.countp (Associated a) ≤ 1) : s.Prod ∣ n :=
  by
  induction' s using Multiset.induction_on with a s induct n primes divs generalizing n
  · simp only [Multiset.prod_zero, one_dvd]
  · rw [Multiset.prod_cons]
    obtain ⟨k, rfl⟩ : a ∣ n := div a (Multiset.mem_cons_self a s)
    apply mul_dvd_mul_left a
    refine'
      induct (fun a ha => h a (Multiset.mem_cons_of_mem ha))
        (fun a => (Multiset.countp_le_of_le _ (Multiset.le_cons_self _ _)).trans (uniq a)) k
        fun b b_in_s => _
    · have b_div_n := div b (Multiset.mem_cons_of_mem b_in_s)
      have a_prime := h a (Multiset.mem_cons_self a s)
      have b_prime := h b (Multiset.mem_cons_of_mem b_in_s)
      refine' (b_prime.dvd_or_dvd b_div_n).resolve_left fun b_div_a => _
      have assoc := b_prime.associated_of_dvd a_prime b_div_a
      have := uniq a
      rw [Multiset.countp_cons_of_pos _ (Associated.refl _), Nat.succ_le_succ_iff, ← not_lt,
        Multiset.countp_pos] at this
      exact this ⟨b, b_in_s, assoc.symm⟩
#align multiset.prod_primes_dvd Multiset.prod_primes_dvd
-/

#print Finset.prod_primes_dvd /-
theorem Finset.prod_primes_dvd [CancelCommMonoidWithZero α] [Unique αˣ] {s : Finset α} (n : α)
    (h : ∀ a ∈ s, Prime a) (div : ∀ a ∈ s, a ∣ n) : (∏ p in s, p) ∣ n := by
  classical exact
      Multiset.prod_primes_dvd n (by simpa only [Multiset.map_id', Finset.mem_def] using h)
        (by simpa only [Multiset.map_id', Finset.mem_def] using div)
        (by
          simp only [Multiset.map_id', associated_eq_eq, Multiset.countp_eq_card_filter, ←
            Multiset.count_eq_card_filter_eq, ← Multiset.nodup_iff_count_le_one, s.nodup])
#align finset.prod_primes_dvd Finset.prod_primes_dvd
-/

namespace Associates

section CommMonoid

variable [CommMonoid α]

/- warning: associates.prod_mk -> Associates.prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1) (Multiset.map.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) p)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (Multiset.prod.{u1} α _inst_1 p))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1) (Multiset.map.{u1, u1} α (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) p)) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (Multiset.prod.{u1} α _inst_1 p))
Case conversion may be inaccurate. Consider using '#align associates.prod_mk Associates.prod_mkₓ'. -/
theorem prod_mk {p : Multiset α} : (p.map Associates.mk).Prod = Associates.mk p.Prod :=
  Multiset.induction_on p (by simp) fun a s ih => by simp [ih, Associates.mk_mul_mk]
#align associates.prod_mk Associates.prod_mk

/- warning: associates.finset_prod_mk -> Associates.finset_prod_mk is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] {p : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Finset.prod.{u1, u2} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) β (Associates.commMonoid.{u1} α _inst_1) p (fun (i : β) => Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (f i))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (Finset.prod.{u1, u2} α β _inst_1 p (fun (i : β) => f i)))
but is expected to have type
  forall {α : Type.{u1}} {β : Type.{u2}} [_inst_1 : CommMonoid.{u1} α] {p : Finset.{u2} β} {f : β -> α}, Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Finset.prod.{u1, u2} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) β (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1) p (fun (i : β) => Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (f i))) (Associates.mk.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1) (Finset.prod.{u1, u2} α β _inst_1 p (fun (i : β) => f i)))
Case conversion may be inaccurate. Consider using '#align associates.finset_prod_mk Associates.finset_prod_mkₓ'. -/
theorem finset_prod_mk {p : Finset β} {f : β → α} :
    (∏ i in p, Associates.mk (f i)) = Associates.mk (∏ i in p, f i) := by
  rw [Finset.prod_eq_multiset_prod, ← Multiset.map_map, prod_mk, ← Finset.prod_eq_multiset_prod]
#align associates.finset_prod_mk Associates.finset_prod_mk

#print Associates.rel_associated_iff_map_eq_map /-
theorem rel_associated_iff_map_eq_map {p q : Multiset α} :
    Multiset.Rel Associated p q ↔ p.map Associates.mk = q.map Associates.mk :=
  by
  rw [← Multiset.rel_eq, Multiset.rel_map]
  simp only [mk_eq_mk_iff_associated]
#align associates.rel_associated_iff_map_eq_map Associates.rel_associated_iff_map_eq_map
-/

/- warning: associates.prod_eq_one_iff -> Associates.prod_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, Iff (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1) p) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))) (forall (a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)), (Membership.Mem.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.hasMem.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a p) -> (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (OfNat.mk.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.one.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.hasOne.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, Iff (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1) p) (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) (forall (a : Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)), (Membership.mem.{u1, u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.instMembershipMultiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) a p) -> (Eq.{succ u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) a (OfNat.ofNat.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) 1 (One.toOfNat1.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instOneAssociates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))))
Case conversion may be inaccurate. Consider using '#align associates.prod_eq_one_iff Associates.prod_eq_one_iffₓ'. -/
theorem prod_eq_one_iff {p : Multiset (Associates α)} :
    p.Prod = 1 ↔ ∀ a ∈ p, (a : Associates α) = 1 :=
  Multiset.induction_on p (by simp)
    (by simp (config := { contextual := true }) [mul_eq_one_iff, or_imp, forall_and])
#align associates.prod_eq_one_iff Associates.prod_eq_one_iff

/- warning: associates.prod_le_prod -> Associates.prod_le_prod is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))} {q : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, (LE.le.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Preorder.toLE.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.partialOrder.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) p q) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.preorder.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1) p) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.commMonoid.{u1} α _inst_1) q))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CommMonoid.{u1} α] {p : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))} {q : Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))}, (LE.le.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Preorder.toLE.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (PartialOrder.toPreorder.{u1} (Multiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))) (Multiset.instPartialOrderMultiset.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1))))) p q) -> (LE.le.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Preorder.toLE.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instPreorderAssociatesToMonoid.{u1} α _inst_1)) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1) p) (Multiset.prod.{u1} (Associates.{u1} α (CommMonoid.toMonoid.{u1} α _inst_1)) (Associates.instCommMonoidAssociatesToMonoid.{u1} α _inst_1) q))
Case conversion may be inaccurate. Consider using '#align associates.prod_le_prod Associates.prod_le_prodₓ'. -/
theorem prod_le_prod {p q : Multiset (Associates α)} (h : p ≤ q) : p.Prod ≤ q.Prod :=
  by
  haveI := Classical.decEq (Associates α)
  haveI := Classical.decEq α
  suffices p.prod ≤ (p + (q - p)).Prod by rwa [add_tsub_cancel_of_le h] at this
  suffices p.prod * 1 ≤ p.prod * (q - p).Prod by simpa
  exact mul_mono (le_refl p.prod) one_le
#align associates.prod_le_prod Associates.prod_le_prod

end CommMonoid

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

/- warning: associates.exists_mem_multiset_le_of_prime -> Associates.exists_mem_multiset_le_of_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {s : Multiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))} {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.commMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) p) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.commMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s)) -> (Exists.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => Exists.{0} (Membership.Mem.{u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Multiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Multiset.hasMem.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a s) (fun (H : Membership.Mem.{u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Multiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Multiset.hasMem.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a s) => LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.preorder.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p a)))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] {s : Multiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))} {p : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))}, (Prime.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instCommMonoidWithZeroAssociatesToMonoidToMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) p) -> (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p (Multiset.prod.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instCommMonoidAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))) s)) -> (Exists.{succ u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (fun (a : Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) => And (Membership.mem.{u1, u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Multiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) (Multiset.instMembershipMultiset.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1))))) a s) (LE.le.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Preorder.toLE.{u1} (Associates.{u1} α (MonoidWithZero.toMonoid.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) (Associates.instPreorderAssociatesToMonoid.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))) p a)))
Case conversion may be inaccurate. Consider using '#align associates.exists_mem_multiset_le_of_prime Associates.exists_mem_multiset_le_of_primeₓ'. -/
theorem exists_mem_multiset_le_of_prime {s : Multiset (Associates α)} {p : Associates α}
    (hp : Prime p) : p ≤ s.Prod → ∃ a ∈ s, p ≤ a :=
  Multiset.induction_on s (fun ⟨d, Eq⟩ => (hp.ne_one (mul_eq_one_iff.1 Eq.symm).1).elim)
    fun a s ih h =>
    have : p ≤ a * s.Prod := by simpa using h
    match Prime.le_or_le hp this with
    | Or.inl h => ⟨a, Multiset.mem_cons_self a s, h⟩
    | Or.inr h =>
      let ⟨a, has, h⟩ := ih h
      ⟨a, Multiset.mem_cons_of_mem has, h⟩
#align associates.exists_mem_multiset_le_of_prime Associates.exists_mem_multiset_le_of_prime

end CancelCommMonoidWithZero

end Associates

namespace Multiset

/- warning: multiset.prod_ne_zero_of_prime -> Multiset.prod_ne_zero_of_prime is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α] (s : Multiset.{u1} α), (forall (x : α), (Membership.Mem.{u1, u1} α (Multiset.{u1} α) (Multiset.hasMem.{u1} α) x s) -> (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) x)) -> (Ne.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) s) (OfNat.ofNat.{u1} α 0 (OfNat.mk.{u1} α 0 (Zero.zero.{u1} α (MulZeroClass.toHasZero.{u1} α (MulZeroOneClass.toMulZeroClass.{u1} α (MonoidWithZero.toMulZeroOneClass.{u1} α (CommMonoidWithZero.toMonoidWithZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} α] [_inst_2 : Nontrivial.{u1} α] (s : Multiset.{u1} α), (forall (x : α), (Membership.mem.{u1, u1} α (Multiset.{u1} α) (Multiset.instMembershipMultiset.{u1} α) x s) -> (Prime.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1) x)) -> (Ne.{succ u1} α (Multiset.prod.{u1} α (CommMonoidWithZero.toCommMonoid.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)) s) (OfNat.ofNat.{u1} α 0 (Zero.toOfNat0.{u1} α (CommMonoidWithZero.toZero.{u1} α (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} α _inst_1)))))
Case conversion may be inaccurate. Consider using '#align multiset.prod_ne_zero_of_prime Multiset.prod_ne_zero_of_primeₓ'. -/
theorem prod_ne_zero_of_prime [CancelCommMonoidWithZero α] [Nontrivial α] (s : Multiset α)
    (h : ∀ x ∈ s, Prime x) : s.Prod ≠ 0 :=
  Multiset.prod_ne_zero fun h0 => Prime.ne_zero (h 0 h0) rfl
#align multiset.prod_ne_zero_of_prime Multiset.prod_ne_zero_of_prime

end Multiset

open Finset Finsupp

section CommMonoidWithZero

variable {M : Type _} [CommMonoidWithZero M]

/- warning: prime.dvd_finset_prod_iff -> Prime.dvd_finset_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u2} M] {S : Finset.{u1} α} {p : M}, (Prime.{u2} M _inst_1 p) -> (forall (g : α -> M), Iff (Dvd.Dvd.{u2} M (semigroupDvd.{u2} M (SemigroupWithZero.toSemigroup.{u2} M (MonoidWithZero.toSemigroupWithZero.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1)))) p (Finset.prod.{u2, u1} M α (CommMonoidWithZero.toCommMonoid.{u2} M _inst_1) S g)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a S) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a S) => Dvd.Dvd.{u2} M (semigroupDvd.{u2} M (SemigroupWithZero.toSemigroup.{u2} M (MonoidWithZero.toSemigroupWithZero.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1)))) p (g a)))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {S : Finset.{u2} α} {p : M}, (Prime.{u1} M _inst_1 p) -> (forall (g : α -> M), Iff (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (Finset.prod.{u1, u2} M α (CommMonoidWithZero.toCommMonoid.{u1} M _inst_1) S g)) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a S) (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (g a)))))
Case conversion may be inaccurate. Consider using '#align prime.dvd_finset_prod_iff Prime.dvd_finset_prod_iffₓ'. -/
theorem Prime.dvd_finset_prod_iff {S : Finset α} {p : M} (pp : Prime p) (g : α → M) :
    p ∣ S.Prod g ↔ ∃ a ∈ S, p ∣ g a :=
  ⟨pp.exists_mem_finset_dvd, fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod_of_mem g ha1)⟩
#align prime.dvd_finset_prod_iff Prime.dvd_finset_prod_iff

/- warning: prime.dvd_finsupp_prod_iff -> Prime.dvd_finsupp_prod_iff is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {M : Type.{u2}} [_inst_1 : CommMonoidWithZero.{u2} M] {f : Finsupp.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1))))} {g : α -> M -> Nat} {p : Nat}, (Prime.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) p) -> (Iff (Dvd.Dvd.{0} Nat Nat.hasDvd p (Finsupp.prod.{u1, u2, 0} α M Nat (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1)))) Nat.commMonoid f g)) (Exists.{succ u1} α (fun (a : α) => Exists.{0} (Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1)))) f)) (fun (H : Membership.Mem.{u1, u1} α (Finset.{u1} α) (Finset.hasMem.{u1} α) a (Finsupp.support.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1)))) f)) => Dvd.Dvd.{0} Nat Nat.hasDvd p (g a (coeFn.{max (succ u1) (succ u2), max (succ u1) (succ u2)} (Finsupp.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1))))) (fun (_x : Finsupp.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1))))) => α -> M) (Finsupp.hasCoeToFun.{u1, u2} α M (MulZeroClass.toHasZero.{u2} M (MulZeroOneClass.toMulZeroClass.{u2} M (MonoidWithZero.toMulZeroOneClass.{u2} M (CommMonoidWithZero.toMonoidWithZero.{u2} M _inst_1))))) f a))))))
but is expected to have type
  forall {α : Type.{u2}} {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {f : Finsupp.{u2, u1} α M (CommMonoidWithZero.toZero.{u1} M _inst_1)} {g : α -> M -> Nat} {p : Nat}, (Prime.{0} Nat (LinearOrderedCommMonoidWithZero.toCommMonoidWithZero.{0} Nat Nat.linearOrderedCommMonoidWithZero) p) -> (Iff (Dvd.dvd.{0} Nat Nat.instDvdNat p (Finsupp.prod.{u2, u1, 0} α M Nat (CommMonoidWithZero.toZero.{u1} M _inst_1) Nat.commMonoid f g)) (Exists.{succ u2} α (fun (a : α) => And (Membership.mem.{u2, u2} α (Finset.{u2} α) (Finset.instMembershipFinset.{u2} α) a (Finsupp.support.{u2, u1} α M (CommMonoidWithZero.toZero.{u1} M _inst_1) f)) (Dvd.dvd.{0} Nat Nat.instDvdNat p (g a (FunLike.coe.{max (succ u2) (succ u1), succ u2, succ u1} (Finsupp.{u2, u1} α M (CommMonoidWithZero.toZero.{u1} M _inst_1)) α (fun (a : α) => (fun (x._@.Mathlib.Data.Finsupp.Defs._hyg.779 : α) => M) a) (Finsupp.funLike.{u2, u1} α M (CommMonoidWithZero.toZero.{u1} M _inst_1)) f a))))))
Case conversion may be inaccurate. Consider using '#align prime.dvd_finsupp_prod_iff Prime.dvd_finsupp_prod_iffₓ'. -/
theorem Prime.dvd_finsupp_prod_iff {f : α →₀ M} {g : α → M → ℕ} {p : ℕ} (pp : Prime p) :
    p ∣ f.Prod g ↔ ∃ a ∈ f.support, p ∣ g a (f a) :=
  Prime.dvd_finset_prod_iff pp _
#align prime.dvd_finsupp_prod_iff Prime.dvd_finsupp_prod_iff

end CommMonoidWithZero

