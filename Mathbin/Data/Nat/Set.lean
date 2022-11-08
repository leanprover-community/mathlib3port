/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Data.Set.Basic

/-!
### Recursion on the natural numbers and `set.range`
-/


namespace Nat

section Set

open Set

theorem zero_union_range_succ : {0} ∪ Range succ = univ := by
  ext n
  cases n <;> simp

@[simp]
protected theorem range_succ : Range succ = { i | 0 < i } := by ext (_ | i) <;> simp [succ_pos, succ_ne_zero]

variable {α : Type _}

theorem range_of_succ (f : ℕ → α) : {f 0} ∪ Range (f ∘ succ) = Range f := by
  rw [← image_singleton, range_comp, ← image_union, zero_union_range_succ, image_univ]

theorem range_rec {α : Type _} (x : α) (f : ℕ → α → α) :
    (Set.Range fun n => Nat.rec x f n : Set α) = {x} ∪ Set.Range fun n => Nat.rec (f 0 x) (f ∘ succ) n := by
  convert (range_of_succ _).symm
  ext n
  induction' n with n ihn
  · rfl
    
  · dsimp at ihn⊢
    rw [ihn]
    

theorem range_cases_on {α : Type _} (x : α) (f : ℕ → α) :
    (Set.Range fun n => Nat.casesOn n x f : Set α) = {x} ∪ Set.Range f :=
  (range_of_succ _).symm

end Set

end Nat

