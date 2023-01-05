/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.vector
! leanprover-community/mathlib commit 5a3e819569b0f12cbec59d740a2613018e7b8eec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Pi
import Mathbin.Data.Array.Lemmas
import Mathbin.Data.Sym.Basic

/-!
# `vector α n` is a fintype when `α` is.
-/


variable {α : Type _}

instance DArray.fintype {n : ℕ} {α : Fin n → Type _} [∀ n, Fintype (α n)] : Fintype (DArray n α) :=
  Fintype.ofEquiv _ (Equiv.dArrayEquivFin _).symm
#align d_array.fintype DArray.fintype

instance Array'.fintype {n : ℕ} {α : Type _} [Fintype α] : Fintype (Array' n α) :=
  DArray.fintype
#align array.fintype Array'.fintype

instance Vector.fintype [Fintype α] {n : ℕ} : Fintype (Vector α n) :=
  Fintype.ofEquiv _ (Equiv.vectorEquivFin _ _).symm
#align vector.fintype Vector.fintype

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym.Sym' α n) :=
  Quotient.fintype _

instance [DecidableEq α] [Fintype α] {n : ℕ} : Fintype (Sym α n) :=
  Fintype.ofEquiv _ Sym.symEquivSym'.symm

