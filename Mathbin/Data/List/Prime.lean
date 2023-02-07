/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen

! This file was ported from Lean 3 source module data.list.prime
! leanprover-community/mathlib commit 0a0ec35061ed9960bf0e7ffb0335f44447b58977
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.Associated
import Mathbin.Data.List.BigOperators.Lemmas
import Mathbin.Data.List.Perm

/-!
# Products of lists of prime elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some theorems relating `prime` and products of `list`s.

-/


open List

section CommMonoidWithZero

variable {M : Type _} [CommMonoidWithZero M]

/- warning: prime.dvd_prod_iff -> Prime.dvd_prod_iff is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {p : M} {L : List.{u1} M}, (Prime.{u1} M _inst_1 p) -> (Iff (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (List.prod.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) L)) (Exists.{succ u1} M (fun (a : M) => Exists.{0} (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a L) (fun (H : Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a L) => Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p a))))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {p : M} {L : List.{u1} M}, (Prime.{u1} M _inst_1 p) -> (Iff (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (List.prod.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Monoid.toOne.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1))) L)) (Exists.{succ u1} M (fun (a : M) => And (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a L) (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p a))))
Case conversion may be inaccurate. Consider using '#align prime.dvd_prod_iff Prime.dvd_prod_iffₓ'. -/
/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
theorem Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime p) : p ∣ L.Prod ↔ ∃ a ∈ L, p ∣ a :=
  by
  constructor
  · intro h
    induction' L with L_hd L_tl L_ih
    · rw [prod_nil] at h
      exact absurd h pp.not_dvd_one
    · rw [prod_cons] at h
      cases' pp.dvd_or_dvd h with hd hd
      · exact ⟨L_hd, mem_cons_self L_hd L_tl, hd⟩
      · obtain ⟨x, hx1, hx2⟩ := L_ih hd
        exact ⟨x, mem_cons_of_mem L_hd hx1, hx2⟩
  · exact fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod ha1)
#align prime.dvd_prod_iff Prime.dvd_prod_iff

/- warning: prime.not_dvd_prod -> Prime.not_dvd_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {p : M} {L : List.{u1} M}, (Prime.{u1} M _inst_1 p) -> (forall (a : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) a L) -> (Not (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p a))) -> (Not (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (List.prod.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) L)))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CommMonoidWithZero.{u1} M] {p : M} {L : List.{u1} M}, (Prime.{u1} M _inst_1 p) -> (forall (a : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) a L) -> (Not (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p a))) -> (Not (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) p (List.prod.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1)))) (Monoid.toOne.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M _inst_1))) L)))
Case conversion may be inaccurate. Consider using '#align prime.not_dvd_prod Prime.not_dvd_prodₓ'. -/
theorem Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : ∀ a ∈ L, ¬p ∣ a) :
    ¬p ∣ L.Prod :=
  mt (Prime.dvd_prod_iff pp).mp <| not_bex.mpr hL
#align prime.not_dvd_prod Prime.not_dvd_prod

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M : Type _} [CancelCommMonoidWithZero M] [Unique (Units M)]

/- warning: mem_list_primes_of_dvd_prod -> mem_list_primes_of_dvd_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} M] [_inst_2 : Unique.{succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))] {p : M}, (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p) -> (forall {L : List.{u1} M}, (forall (q : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) q L) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) q)) -> (Dvd.Dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) p (List.prod.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) L)) -> (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) p L))
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} M] [_inst_2 : Unique.{succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))] {p : M}, (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p) -> (forall {L : List.{u1} M}, (forall (q : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) q L) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) q)) -> (Dvd.dvd.{u1} M (semigroupDvd.{u1} M (SemigroupWithZero.toSemigroup.{u1} M (MonoidWithZero.toSemigroupWithZero.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) p (List.prod.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (Monoid.toOne.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1)))) L)) -> (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) p L))
Case conversion may be inaccurate. Consider using '#align mem_list_primes_of_dvd_prod mem_list_primes_of_dvd_prodₓ'. -/
theorem mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : ∀ q ∈ L, Prime q)
    (hpL : p ∣ L.Prod) : p ∈ L :=
  by
  obtain ⟨x, hx1, hx2⟩ := hp.dvd_prod_iff.mp hpL
  rwa [(prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2]
#align mem_list_primes_of_dvd_prod mem_list_primes_of_dvd_prod

/- warning: perm_of_prod_eq_prod -> perm_of_prod_eq_prod is a dubious translation:
lean 3 declaration is
  forall {M : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} M] [_inst_2 : Unique.{succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (Eq.{succ u1} M (List.prod.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) l₁) (List.prod.{u1} M (MulZeroClass.toHasMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (MulOneClass.toHasOne.{u1} M (MulZeroOneClass.toMulOneClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) l₂)) -> (forall (p : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) p l₁) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p)) -> (forall (p : M), (Membership.Mem.{u1, u1} M (List.{u1} M) (List.hasMem.{u1} M) p l₂) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p)) -> (List.Perm.{u1} M l₁ l₂)
but is expected to have type
  forall {M : Type.{u1}} [_inst_1 : CancelCommMonoidWithZero.{u1} M] [_inst_2 : Unique.{succ u1} (Units.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))] {l₁ : List.{u1} M} {l₂ : List.{u1} M}, (Eq.{succ u1} M (List.prod.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (Monoid.toOne.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1)))) l₁) (List.prod.{u1} M (MulZeroClass.toMul.{u1} M (MulZeroOneClass.toMulZeroClass.{u1} M (MonoidWithZero.toMulZeroOneClass.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1))))) (Monoid.toOne.{u1} M (MonoidWithZero.toMonoid.{u1} M (CommMonoidWithZero.toMonoidWithZero.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1)))) l₂)) -> (forall (p : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) p l₁) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p)) -> (forall (p : M), (Membership.mem.{u1, u1} M (List.{u1} M) (List.instMembershipList.{u1} M) p l₂) -> (Prime.{u1} M (CancelCommMonoidWithZero.toCommMonoidWithZero.{u1} M _inst_1) p)) -> (List.Perm.{u1} M l₁ l₂)
Case conversion may be inaccurate. Consider using '#align perm_of_prod_eq_prod perm_of_prod_eq_prodₓ'. -/
theorem perm_of_prod_eq_prod :
    ∀ {l₁ l₂ : List M}, l₁.Prod = l₂.Prod → (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) → Perm l₁ l₂
  | [], [], _, _, _ => Perm.nil
  | [], a :: l, h₁, h₂, h₃ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
  | a :: l, [], h₁, h₂, h₃ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
  | a :: l₁, b :: l₂, h, hl₁, hl₂ => by
    classical
      have hl₁' : ∀ p ∈ l₁, Prime p := fun p hp => hl₁ p (mem_cons_of_mem _ hp)
      have hl₂' : ∀ p ∈ (b :: l₂).eraseₓ a, Prime p := fun p hp => hl₂ p (mem_of_mem_erase hp)
      have ha : a ∈ b :: l₂ :=
        mem_list_primes_of_dvd_prod (hl₁ a (mem_cons_self _ _)) hl₂
          (h ▸ by rw [prod_cons] <;> exact dvd_mul_right _ _)
      have hb : b :: l₂ ~ a :: (b :: l₂).eraseₓ a := perm_cons_erase ha
      have hl : Prod l₁ = Prod ((b :: l₂).eraseₓ a) :=
        (mul_right_inj' (hl₁ a (mem_cons_self _ _)).NeZero).1 <| by
          rwa [← prod_cons, ← prod_cons, ← hb.prod_eq]
      exact perm.trans ((perm_of_prod_eq_prod hl hl₁' hl₂').cons _) hb.symm
#align perm_of_prod_eq_prod perm_of_prod_eq_prod

end CancelCommMonoidWithZero

