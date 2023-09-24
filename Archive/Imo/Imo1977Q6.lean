/-
Copyright (c) 2021 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
import Data.Pnat.Basic

#align_import imo.imo1977_q6 from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# IMO 1977 Q6

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Suppose `f : ℕ+ → ℕ+` satisfies `f(f(n)) < f(n + 1)` for all `n`.
Prove that `f(n) = n` for all `n`.

We first prove the problem statement for `f : ℕ → ℕ`
then we use it to prove the statement for positive naturals.
-/


namespace imo1977_q6

theorem imo1977_q6_nat (f : ℕ → ℕ) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n :=
  by
  have h' : ∀ k n : ℕ, k ≤ n → k ≤ f n := by
    intro k
    induction' k with k h_ind
    · intros; exact Nat.zero_le _
    · intro n hk
      apply Nat.succ_le_of_lt
      calc
        k ≤ f (f (n - 1)) := h_ind _ (h_ind (n - 1) (le_tsub_of_add_le_right hk))
        _ < f n := tsub_add_cancel_of_le (le_trans (Nat.succ_le_succ (Nat.zero_le _)) hk) ▸ h _
  have hf : ∀ n, n ≤ f n := fun n => h' n n rfl.le
  have hf_mono : StrictMono f := strictMono_nat_of_lt_succ fun _ => lt_of_le_of_lt (hf _) (h _)
  intro
  exact Nat.eq_of_le_of_lt_succ (hf _) (hf_mono.lt_iff_lt.mp (h _))
#align imo1977_q6.imo1977_q6_nat Imo1977Q6.imo1977_q6_nat

end imo1977_q6

open imo1977_q6

theorem imo1977_q6 (f : ℕ+ → ℕ+) (h : ∀ n, f (f n) < f (n + 1)) : ∀ n, f n = n :=
  by
  intro n
  simpa using imo1977_q6_nat (fun m => if 0 < m then f m.toPNat' else 0) _ n
  · intro x; cases x
    · simp
    · simpa using h _
#align imo1977_q6 imo1977_q6

