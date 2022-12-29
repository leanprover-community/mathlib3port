/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.nat.psub
! leanprover-community/mathlib commit 422e70f7ce183d2900c586a8cda8381e788a0c62
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Option.Basic
import Mathbin.Data.Nat.Basic

/-!
# Partial predecessor and partial subtraction on the natural numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> https://github.com/leanprover-community/mathlib4/pull/806
> Any changes to this file require a corresponding PR to mathlib4.

The usual definition of natural number subtraction (`nat.sub`) returns 0 as a "garbage value" for
`a - b` when `a < b`. Similarly, `nat.pred 0` is defined to be `0`. The functions in this file
wrap the result in an `option` type instead:

## Main definitions

- `nat.ppred`: a partial predecessor operation
- `nat.psub`: a partial subtraction operation

-/


namespace Nat

#print Nat.ppred /-
/-- Partial predecessor operation. Returns `ppred n = some m`
  if `n = m + 1`, otherwise `none`. -/
@[simp]
def ppred : ℕ → Option ℕ
  | 0 => none
  | n + 1 => some n
#align nat.ppred Nat.ppred
-/

#print Nat.psub /-
/-- Partial subtraction operation. Returns `psub m n = some k`
  if `m = n + k`, otherwise `none`. -/
@[simp]
def psub (m : ℕ) : ℕ → Option ℕ
  | 0 => some m
  | n + 1 => psub n >>= ppred
#align nat.psub Nat.psub
-/

#print Nat.pred_eq_ppred /-
theorem pred_eq_ppred (n : ℕ) : pred n = (ppred n).getOrElse 0 := by cases n <;> rfl
#align nat.pred_eq_ppred Nat.pred_eq_ppred
-/

#print Nat.sub_eq_psub /-
theorem sub_eq_psub (m : ℕ) : ∀ n, m - n = (psub m n).getOrElse 0
  | 0 => rfl
  | n + 1 => (pred_eq_ppred (m - n)).trans <| by rw [sub_eq_psub, psub] <;> cases psub m n <;> rfl
#align nat.sub_eq_psub Nat.sub_eq_psub
-/

#print Nat.ppred_eq_some /-
@[simp]
theorem ppred_eq_some {m : ℕ} : ∀ {n}, ppred n = some m ↔ succ m = n
  | 0 => by constructor <;> intro h <;> contradiction
  | n + 1 => by dsimp <;> constructor <;> intro h <;> injection h <;> subst n
#align nat.ppred_eq_some Nat.ppred_eq_some
-/

#print Nat.ppred_eq_none /-
@[simp]
theorem ppred_eq_none : ∀ {n : ℕ}, ppred n = none ↔ n = 0
  | 0 => by simp
  | n + 1 => by dsimp <;> constructor <;> contradiction
#align nat.ppred_eq_none Nat.ppred_eq_none
-/

#print Nat.psub_eq_some /-
theorem psub_eq_some {m : ℕ} : ∀ {n k}, psub m n = some k ↔ k + n = m
  | 0, k => by simp [eq_comm]
  | n + 1, k => by
    dsimp
    apply option.bind_eq_some.trans
    simp [psub_eq_some, add_comm, add_left_comm, Nat.succ_eq_add_one]
#align nat.psub_eq_some Nat.psub_eq_some
-/

#print Nat.psub_eq_none /-
theorem psub_eq_none {m n : ℕ} : psub m n = none ↔ m < n :=
  by
  cases s : psub m n <;> simp [eq_comm]
  · show m < n
    refine' lt_of_not_ge fun h => _
    cases' le.dest h with k e
    injection s.symm.trans (psub_eq_some.2 <| (add_comm _ _).trans e)
  · show n ≤ m
    rw [← psub_eq_some.1 s]
    apply Nat.le_add_left
#align nat.psub_eq_none Nat.psub_eq_none
-/

#print Nat.ppred_eq_pred /-
theorem ppred_eq_pred {n} (h : 0 < n) : ppred n = some (pred n) :=
  ppred_eq_some.2 <| succ_pred_eq_of_pos h
#align nat.ppred_eq_pred Nat.ppred_eq_pred
-/

#print Nat.psub_eq_sub /-
theorem psub_eq_sub {m n} (h : n ≤ m) : psub m n = some (m - n) :=
  psub_eq_some.2 <| Nat.sub_add_cancel h
#align nat.psub_eq_sub Nat.psub_eq_sub
-/

/- warning: nat.psub_add -> Nat.psub_add is a dubious translation:
lean 3 declaration is
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} (Option.{0} Nat) (Nat.psub m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n k)) (Bind.bind.{0, 0} Option.{0} (Monad.toHasBind.{0, 0} Option.{0} Option.monad.{0}) Nat Nat (Nat.psub m n) (fun (x : Nat) => Nat.psub x k))
but is expected to have type
  forall (m : Nat) (n : Nat) (k : Nat), Eq.{1} (Option.{0} Nat) (Nat.psub m (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n k)) (Bind.bind.{0, 0} Option.{0} (Monad.toBind.{0, 0} Option.{0} instMonadOption.{0}) Nat Nat (Nat.psub m n) (fun (x : Nat) => Nat.psub x k))
Case conversion may be inaccurate. Consider using '#align nat.psub_add Nat.psub_addₓ'. -/
theorem psub_add (m n k) :
    psub m (n + k) = do
      let x ← psub m n
      psub x k :=
  by induction k <;> simp [*, add_succ, bind_assoc]
#align nat.psub_add Nat.psub_add

#print Nat.psub' /-
/-- Same as `psub`, but with a more efficient implementation. -/
@[inline]
def psub' (m n : ℕ) : Option ℕ :=
  if n ≤ m then some (m - n) else none
#align nat.psub' Nat.psub'
-/

#print Nat.psub'_eq_psub /-
theorem psub'_eq_psub (m n) : psub' m n = psub m n := by
  rw [psub'] <;> split_ifs <;> [exact (psub_eq_sub h).symm,
    exact (psub_eq_none.2 (not_le.1 h)).symm]
#align nat.psub'_eq_psub Nat.psub'_eq_psub
-/

end Nat

