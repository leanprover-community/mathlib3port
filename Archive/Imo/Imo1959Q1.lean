/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker
-/
import Tactic.Ring
import Data.Nat.Prime.Defs

#align_import imo.imo1959_q1 from "leanprover-community/mathlib"@"08b081ea92d80e3a41f899eea36ef6d56e0f1db0"

/-!
# IMO 1959 Q1

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Prove that the fraction `(21n+4)/(14n+3)` is irreducible for every natural number `n`.

Since Lean doesn't have a concept of "irreducible fractions" per se, we just formalize this
as saying the numerator and denominator are relatively prime.
-/


open Nat

namespace imo1959_q1

theorem calculation (n k : ℕ) (h1 : k ∣ 21 * n + 4) (h2 : k ∣ 14 * n + 3) : k ∣ 1 :=
  have h3 : k ∣ 2 * (21 * n + 4) := h1.hMul_left 2
  have h4 : k ∣ 3 * (14 * n + 3) := h2.hMul_left 3
  have h5 : 3 * (14 * n + 3) = 2 * (21 * n + 4) + 1 := by ring
  (Nat.dvd_add_right h3).mp (h5 ▸ h4)
#align imo1959_q1.calculation Imo1959Q1.calculation

end imo1959_q1

open imo1959_q1

theorem imo1959_q1 : ∀ n : ℕ, Coprime (21 * n + 4) (14 * n + 3) := fun n =>
  coprime_of_dvd' fun k hp h1 h2 => calculation n k h1 h2
#align imo1959_q1 imo1959_q1

