/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker, Anne Baanen
-/
import Algebra.Associated
import Data.List.BigOperators.Lemmas
import Data.List.Perm

#align_import data.list.prime from "leanprover-community/mathlib"@"f2f413b9d4be3a02840d0663dace76e8fe3da053"

/-!
# Products of lists of prime elements.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file contains some theorems relating `prime` and products of `list`s.

-/


open List

section CommMonoidWithZero

variable {M : Type _} [CommMonoidWithZero M]

#print Prime.dvd_prod_iff /-
/-- Prime `p` divides the product of a list `L` iff it divides some `a ∈ L` -/
theorem Prime.dvd_prod_iff {p : M} {L : List M} (pp : Prime p) : p ∣ L.Prod ↔ ∃ a ∈ L, p ∣ a :=
  by
  constructor
  · intro h
    induction' L with L_hd L_tl L_ih
    · rw [prod_nil] at h ; exact absurd h pp.not_dvd_one
    · rw [prod_cons] at h 
      cases' pp.dvd_or_dvd h with hd hd
      · exact ⟨L_hd, mem_cons_self L_hd L_tl, hd⟩
      · obtain ⟨x, hx1, hx2⟩ := L_ih hd
        exact ⟨x, mem_cons_of_mem L_hd hx1, hx2⟩
  · exact fun ⟨a, ha1, ha2⟩ => dvd_trans ha2 (dvd_prod ha1)
#align prime.dvd_prod_iff Prime.dvd_prod_iff
-/

#print Prime.not_dvd_prod /-
theorem Prime.not_dvd_prod {p : M} {L : List M} (pp : Prime p) (hL : ∀ a ∈ L, ¬p ∣ a) :
    ¬p ∣ L.Prod :=
  mt (Prime.dvd_prod_iff pp).mp <| not_bex.mpr hL
#align prime.not_dvd_prod Prime.not_dvd_prod
-/

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable {M : Type _} [CancelCommMonoidWithZero M] [Unique (Units M)]

#print mem_list_primes_of_dvd_prod /-
theorem mem_list_primes_of_dvd_prod {p : M} (hp : Prime p) {L : List M} (hL : ∀ q ∈ L, Prime q)
    (hpL : p ∣ L.Prod) : p ∈ L :=
  by
  obtain ⟨x, hx1, hx2⟩ := hp.dvd_prod_iff.mp hpL
  rwa [(prime_dvd_prime_iff_eq hp (hL x hx1)).mp hx2]
#align mem_list_primes_of_dvd_prod mem_list_primes_of_dvd_prod
-/

#print perm_of_prod_eq_prod /-
theorem perm_of_prod_eq_prod :
    ∀ {l₁ l₂ : List M}, l₁.Prod = l₂.Prod → (∀ p ∈ l₁, Prime p) → (∀ p ∈ l₂, Prime p) → Perm l₁ l₂
  | [], [], _, _, _ => Perm.nil
  | [], a :: l, h₁, h₂, h₃ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁.symm ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₃ a (mem_cons_self _ _)))
  | a :: l, [], h₁, h₂, h₃ =>
    have ha : a ∣ 1 := @prod_nil M _ ▸ h₁ ▸ (@prod_cons _ _ l a).symm ▸ dvd_mul_right _ _
    absurd ha (Prime.not_dvd_one (h₂ a (mem_cons_self _ _)))
  | a :: l₁, b :: l₂, h, hl₁, hl₂ => by classical
#align perm_of_prod_eq_prod perm_of_prod_eq_prod
-/

end CancelCommMonoidWithZero

