/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Multiset.Powerset

#align_import data.multiset.antidiagonal from "leanprover-community/mathlib"@"e04043d6bf7264a3c84bc69711dc354958ca4516"

/-!
# The antidiagonal on a multiset.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/


namespace Multiset

open List

variable {α β : Type _}

#print Multiset.antidiagonal /-
/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l => (revzip (powersetAux l) : Multiset (Multiset α × Multiset α)))
    fun l₁ l₂ h => Quot.sound (revzip_powersetAux_perm h)
#align multiset.antidiagonal Multiset.antidiagonal
-/

#print Multiset.antidiagonal_coe /-
theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzip (powersetAux l) :=
  rfl
#align multiset.antidiagonal_coe Multiset.antidiagonal_coe
-/

#print Multiset.antidiagonal_coe' /-
@[simp]
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzip (powersetAux' l) :=
  Quot.sound revzip_powersetAux_perm_aux'
#align multiset.antidiagonal_coe' Multiset.antidiagonal_coe'
-/

#print Multiset.mem_antidiagonal /-
/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} :
    x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
  Quotient.inductionOn s fun l => by
    simp [antidiagonal_coe]; refine' ⟨fun h => revzip_powerset_aux h, fun h => _⟩
    haveI := Classical.decEq α
    simp [revzip_powerset_aux_lemma l revzip_powerset_aux, h.symm]
    cases' x with x₁ x₂
    dsimp only
    exact ⟨x₁, le_add_right _ _, by rw [add_tsub_cancel_left x₁ x₂]⟩
#align multiset.mem_antidiagonal Multiset.mem_antidiagonal
-/

#print Multiset.antidiagonal_map_fst /-
@[simp]
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  Quotient.inductionOn s fun l => by simp [powerset_aux']
#align multiset.antidiagonal_map_fst Multiset.antidiagonal_map_fst
-/

#print Multiset.antidiagonal_map_snd /-
@[simp]
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  Quotient.inductionOn s fun l => by simp [powerset_aux']
#align multiset.antidiagonal_map_snd Multiset.antidiagonal_map_snd
-/

#print Multiset.antidiagonal_zero /-
@[simp]
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl
#align multiset.antidiagonal_zero Multiset.antidiagonal_zero
-/

#print Multiset.antidiagonal_cons /-
@[simp]
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  Quotient.inductionOn s fun l =>
    by
    simp only [revzip, reverse_append, quot_mk_to_coe, coe_eq_coe, powerset_aux'_cons, cons_coe,
      coe_map, antidiagonal_coe', coe_add]
    rw [← zip_map, ← zip_map, zip_append, (_ : _ ++ _ = _)]
    · congr <;> simp; · simp
#align multiset.antidiagonal_cons Multiset.antidiagonal_cons
-/

#print Multiset.antidiagonal_eq_map_powerset /-
theorem antidiagonal_eq_map_powerset [DecidableEq α] (s : Multiset α) :
    s.antidiagonal = s.powerset.map fun t => (s - t, t) :=
  by
  induction' s using Multiset.induction_on with a s hs
  · simp only [antidiagonal_zero, powerset_zero, zero_tsub, map_singleton]
  · simp_rw [antidiagonal_cons, powerset_cons, map_add, hs, map_map, Function.comp, Prod.map_mk,
      id.def, sub_cons, erase_cons_head]
    rw [add_comm]
    congr 1
    refine' Multiset.map_congr rfl fun x hx => _
    rw [cons_sub_of_le _ (mem_powerset.mp hx)]
#align multiset.antidiagonal_eq_map_powerset Multiset.antidiagonal_eq_map_powerset
-/

#print Multiset.card_antidiagonal /-
@[simp]
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s <;> rwa [← antidiagonal_map_fst, card_map] at this
#align multiset.card_antidiagonal Multiset.card_antidiagonal
-/

#print Multiset.prod_map_add /-
theorem prod_map_add [CommSemiring β] {s : Multiset α} {f g : α → β} :
    prod (s.map fun a => f a + g a) =
      sum ((antidiagonal s).map fun p => (p.1.map f).Prod * (p.2.map g).Prod) :=
  by
  refine' s.induction_on _ _
  · simp
  · intro a s ih
    have := @sum_map_mul_left α β _
    simp [ih, add_mul, mul_comm, mul_left_comm (f a), mul_left_comm (g a), mul_assoc,
      sum_map_mul_left.symm]
    cc
#align multiset.prod_map_add Multiset.prod_map_add
-/

end Multiset

