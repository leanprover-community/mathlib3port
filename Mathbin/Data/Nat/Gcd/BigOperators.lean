/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

! This file was ported from Lean 3 source module data.nat.gcd.big_operators
! leanprover-community/mathlib commit dc6c365e751e34d100e80fe6e314c3c3e0fd2988
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Gcd.Basic
import Mathbin.Algebra.BigOperators.Basic

/-! # Lemmas about coprimality with big products.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

These lemmas are kept separate from `data.nat.gcd.basic` in order to minimize imports.
-/


namespace Nat

open BigOperators

#print Nat.coprime_prod_left /-
/-- See `is_coprime.prod_left` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_left {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → coprime (s i) x) → coprime (∏ i : ι in t, s i) x :=
  Finset.prod_induction s (fun y => y.coprime x) (fun a b => coprime.mul) (by simp)
#align nat.coprime_prod_left Nat.coprime_prod_left
-/

#print Nat.coprime_prod_right /-
/-- See `is_coprime.prod_right` for the corresponding lemma about `is_coprime` -/
theorem coprime_prod_right {ι : Type _} {x : ℕ} {s : ι → ℕ} {t : Finset ι} :
    (∀ i : ι, i ∈ t → coprime x (s i)) → coprime x (∏ i : ι in t, s i) :=
  Finset.prod_induction s (fun y => x.coprime y) (fun a b => coprime.mul_right) (by simp)
#align nat.coprime_prod_right Nat.coprime_prod_right
-/

end Nat

