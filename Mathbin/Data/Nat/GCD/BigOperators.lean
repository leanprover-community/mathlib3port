/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import Data.Nat.GCD.Basic
import Algebra.BigOperators.Group.Finset

#align_import data.nat.gcd.big_operators from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-! # Lemmas about coprimality with big products.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are kept separate from `data.nat.gcd.basic` in order to minimize imports.
-/


namespace Nat

open scoped BigOperators

#print Nat.Coprime.prod_left /-
/-- See `is_coprime.prod_left` for the corresponding lemma about `is_coprime` -/
theorem Nat.Coprime.prod_left {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime (s i) x) → Coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y => y.Coprime x) (fun a b => Coprime.mul) (by simp)
#align nat.coprime_prod_left Nat.Coprime.prod_left
-/

#print Nat.Coprime.prod_right /-
/-- See `is_coprime.prod_right` for the corresponding lemma about `is_coprime` -/
theorem Nat.Coprime.prod_right {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → Coprime x (s i)) → Coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y => x.Coprime y) (fun a b => Coprime.mul_right) (by simp)
#align nat.coprime_prod_right Nat.Coprime.prod_right
-/

end Nat

