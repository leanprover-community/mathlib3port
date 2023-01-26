/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.sigma.interval
! leanprover-community/mathlib commit f93c11933efbc3c2f0299e47b8ff83e9b539cbf6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Sigma.Order
import Mathbin.Order.LocallyFinite

/-!
# Finite intervals in a sigma type

This file provides the `locally_finite_order` instance for the disjoint sum of orders `Σ i, α i` and
calculates the cardinality of its finite intervals.

## TODO

Do the same for the lexicographical order
-/


open Finset Function

namespace Sigma

variable {ι : Type _} {α : ι → Type _}

/-! ### Disjoint sum of orders -/


section Disjoint

variable [DecidableEq ι] [∀ i, Preorder (α i)] [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (Σi, α i)
    where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact bex_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σi, α i)

theorem card_icc : (Icc a b).card = if h : a.1 = b.1 then (Icc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Icc Sigma.card_icc

theorem card_ico : (Ico a b).card = if h : a.1 = b.1 then (Ico (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ico Sigma.card_ico

theorem card_ioc : (Ioc a b).card = if h : a.1 = b.1 then (Ioc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioc Sigma.card_ioc

theorem card_ioo : (Ioo a b).card = if h : a.1 = b.1 then (Ioo (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioo Sigma.card_ioo

end

variable (i : ι) (a b : α i)

@[simp]
theorem icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Icc_mk_mk Sigma.icc_mk_mk

@[simp]
theorem ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ico_mk_mk Sigma.ico_mk_mk

@[simp]
theorem ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioc_mk_mk Sigma.ioc_mk_mk

@[simp]
theorem ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioo_mk_mk Sigma.ioo_mk_mk

end Disjoint

end Sigma

