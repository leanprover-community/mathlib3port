/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.pi.interval
! leanprover-community/mathlib commit 861a26926586cd46ff80264d121cdb6fa0e35cc1
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.LocallyFinite
import Mathbin.Data.Fintype.BigOperators

/-!
# Intervals in a pi type

This file shows that (dependent) functions to locally finite orders equipped with the pointwise
order are locally finite and calculates the cardinality of their intervals.
-/


open Finset Fintype

open BigOperators

variable {ι : Type _} {α : ι → Type _}

namespace Pi

section LocallyFinite

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]
  [∀ i, LocallyFiniteOrder (α i)]

instance : LocallyFiniteOrder (∀ i, α i) :=
  LocallyFiniteOrder.ofIcc _ (fun a b => pi_finset fun i => Icc (a i) (b i)) fun a b x => by
    simp_rw [mem_pi_finset, mem_Icc, le_def, forall_and]

variable (a b : ∀ i, α i)

theorem icc_eq : Icc a b = piFinset fun i => Icc (a i) (b i) :=
  rfl
#align pi.Icc_eq Pi.icc_eq

theorem card_icc : (Icc a b).card = ∏ i, (Icc (a i) (b i)).card :=
  card_piFinset _
#align pi.card_Icc Pi.card_icc

theorem card_ico : (Ico a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ico_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ico Pi.card_ico

theorem card_ioc : (Ioc a b).card = (∏ i, (Icc (a i) (b i)).card) - 1 := by
  rw [card_Ioc_eq_card_Icc_sub_one, card_Icc]
#align pi.card_Ioc Pi.card_ioc

theorem card_ioo : (Ioo a b).card = (∏ i, (Icc (a i) (b i)).card) - 2 := by
  rw [card_Ioo_eq_card_Icc_sub_two, card_Icc]
#align pi.card_Ioo Pi.card_ioo

end LocallyFinite

section Bounded

variable [DecidableEq ι] [Fintype ι] [∀ i, DecidableEq (α i)] [∀ i, PartialOrder (α i)]

section Bot

variable [∀ i, LocallyFiniteOrderBot (α i)] (b : ∀ i, α i)

instance : LocallyFiniteOrderBot (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIic _ (fun b => pi_finset fun i => Iic (b i)) fun b x => by
    simp_rw [mem_pi_finset, mem_Iic, le_def]

theorem card_iic : (Iic b).card = ∏ i, (Iic (b i)).card :=
  card_piFinset _
#align pi.card_Iic Pi.card_iic

theorem card_iio : (Iio b).card = (∏ i, (Iic (b i)).card) - 1 := by
  rw [card_Iio_eq_card_Iic_sub_one, card_Iic]
#align pi.card_Iio Pi.card_iio

end Bot

section Top

variable [∀ i, LocallyFiniteOrderTop (α i)] (a : ∀ i, α i)

instance : LocallyFiniteOrderTop (∀ i, α i) :=
  LocallyFiniteOrderTop.ofIci _ (fun a => pi_finset fun i => Ici (a i)) fun a x => by
    simp_rw [mem_pi_finset, mem_Ici, le_def]

theorem card_ici : (Ici a).card = ∏ i, (Ici (a i)).card :=
  card_piFinset _
#align pi.card_Ici Pi.card_ici

theorem card_ioi : (Ioi a).card = (∏ i, (Ici (a i)).card) - 1 := by
  rw [card_Ioi_eq_card_Ici_sub_one, card_Ici]
#align pi.card_Ioi Pi.card_ioi

end Top

end Bounded

end Pi

