/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Data.Sigma.Order
import Order.Interval.Finset.Defs

#align_import data.sigma.interval from "leanprover-community/mathlib"@"50832daea47b195a48b5b33b1c8b2162c48c3afc"

/-!
# Finite intervals in a sigma type

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

instance : LocallyFiniteOrder (Σ i, α i)
    where
  finsetIcc := sigmaLift fun _ => Icc
  finsetIco := sigmaLift fun _ => Ico
  finsetIoc := sigmaLift fun _ => Ioc
  finsetIoo := sigmaLift fun _ => Ioo
  finset_mem_Icc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, mem_Icc, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ico := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ico, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioc := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, le_def, lt_def, mem_Ioc, exists_and_left, ← exists_and_right, ←
      exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩
  finset_mem_Ioo := fun ⟨i, a⟩ ⟨j, b⟩ ⟨k, c⟩ =>
    by
    simp_rw [mem_sigma_lift, lt_def, mem_Ioo, exists_and_left, ← exists_and_right, ← exists_prop]
    exact exists₂_congr fun _ _ => by constructor <;> rintro ⟨⟨⟩, ht⟩ <;> exact ⟨rfl, ht⟩

section

variable (a b : Σ i, α i)

#print Sigma.card_Icc /-
theorem card_Icc : (Icc a b).card = if h : a.1 = b.1 then (Icc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Icc Sigma.card_Icc
-/

#print Sigma.card_Ico /-
theorem card_Ico : (Ico a b).card = if h : a.1 = b.1 then (Ico (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ico Sigma.card_Ico
-/

#print Sigma.card_Ioc /-
theorem card_Ioc : (Ioc a b).card = if h : a.1 = b.1 then (Ioc (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioc Sigma.card_Ioc
-/

#print Sigma.card_Ioo /-
theorem card_Ioo : (Ioo a b).card = if h : a.1 = b.1 then (Ioo (h.rec a.2) b.2).card else 0 :=
  card_sigmaLift _ _ _
#align sigma.card_Ioo Sigma.card_Ioo
-/

end

variable (i : ι) (a b : α i)

#print Sigma.Icc_mk_mk /-
@[simp]
theorem Icc_mk_mk : Icc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Icc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Icc_mk_mk Sigma.Icc_mk_mk
-/

#print Sigma.Ico_mk_mk /-
@[simp]
theorem Ico_mk_mk : Ico (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ico a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ico_mk_mk Sigma.Ico_mk_mk
-/

#print Sigma.Ioc_mk_mk /-
@[simp]
theorem Ioc_mk_mk : Ioc (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioc a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioc_mk_mk Sigma.Ioc_mk_mk
-/

#print Sigma.Ioo_mk_mk /-
@[simp]
theorem Ioo_mk_mk : Ioo (⟨i, a⟩ : Sigma α) ⟨i, b⟩ = (Ioo a b).map (Embedding.sigmaMk i) :=
  dif_pos rfl
#align sigma.Ioo_mk_mk Sigma.Ioo_mk_mk
-/

end Disjoint

end Sigma

