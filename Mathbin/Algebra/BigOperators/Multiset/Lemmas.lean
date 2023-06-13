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

#print Multiset.prod_eq_one_iff /-
@[to_additive]
theorem prod_eq_one_iff [CanonicallyOrderedMonoid α] {m : Multiset α} :
    m.Prod = 1 ↔ ∀ x ∈ m, x = (1 : α) :=
  Quotient.inductionOn m fun l => by simpa using List.prod_eq_one_iff l
#align multiset.prod_eq_one_iff Multiset.prod_eq_one_iff
#align multiset.sum_eq_zero_iff Multiset.sum_eq_zero_iff
-/

end Multiset

open Multiset

namespace Commute

variable [NonUnitalNonAssocSemiring α] {a : α} {s : Multiset ι} {f : ι → α}

#print Commute.multiset_sum_right /-
theorem multiset_sum_right (s : Multiset α) (a : α) (h : ∀ b ∈ s, Commute a b) : Commute a s.Sum :=
  by
  induction s using Quotient.inductionOn
  rw [quot_mk_to_coe, coe_sum]
  exact Commute.list_sum_right _ _ h
#align commute.multiset_sum_right Commute.multiset_sum_right
-/

#print Commute.multiset_sum_left /-
theorem multiset_sum_left (s : Multiset α) (b : α) (h : ∀ a ∈ s, Commute a b) : Commute s.Sum b :=
  (Commute.multiset_sum_right _ _ fun a ha => (h _ ha).symm).symm
#align commute.multiset_sum_left Commute.multiset_sum_left
-/

end Commute

