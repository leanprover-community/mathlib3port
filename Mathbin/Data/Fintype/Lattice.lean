/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Card
import Data.Finset.Lattice

#align_import data.fintype.lattice from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# Lemmas relating fintypes and order/lattice structure.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


open Function

open scoped Nat

universe u v

variable {α β γ : Type _}

namespace Finset

variable [Fintype α] {s : Finset α}

#print Finset.sup_univ_eq_iSup /-
/-- A special case of `finset.sup_eq_supr` that omits the useless `x ∈ univ` binder. -/
theorem sup_univ_eq_iSup [CompleteLattice β] (f : α → β) : Finset.univ.sup f = iSup f :=
  (sup_eq_iSup _ f).trans <| congr_arg _ <| funext fun a => iSup_pos (mem_univ _)
#align finset.sup_univ_eq_supr Finset.sup_univ_eq_iSup
-/

#print Finset.inf_univ_eq_iInf /-
/-- A special case of `finset.inf_eq_infi` that omits the useless `x ∈ univ` binder. -/
theorem inf_univ_eq_iInf [CompleteLattice β] (f : α → β) : Finset.univ.inf f = iInf f :=
  sup_univ_eq_iSup (f : α → βᵒᵈ)
#align finset.inf_univ_eq_infi Finset.inf_univ_eq_iInf
-/

#print Finset.fold_inf_univ /-
@[simp]
theorem fold_inf_univ [SemilatticeInf α] [OrderBot α] (a : α) :
    (Finset.univ.fold (· ⊓ ·) a fun x => x) = ⊥ :=
  eq_bot_iff.2 <|
    ((Finset.fold_op_rel_iff_and <| @le_inf_iff α _).1 le_rfl).2 ⊥ <| Finset.mem_univ _
#align finset.fold_inf_univ Finset.fold_inf_univ
-/

#print Finset.fold_sup_univ /-
@[simp]
theorem fold_sup_univ [SemilatticeSup α] [OrderTop α] (a : α) :
    (Finset.univ.fold (· ⊔ ·) a fun x => x) = ⊤ :=
  @fold_inf_univ αᵒᵈ ‹Fintype α› _ _ _
#align finset.fold_sup_univ Finset.fold_sup_univ
-/

end Finset

open Finset Function

#print Finite.exists_max /-
theorem Finite.exists_max [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x ≤ f x₀ := by cases nonempty_fintype α;
  simpa using exists_max_image univ f univ_nonempty
#align finite.exists_max Finite.exists_max
-/

#print Finite.exists_min /-
theorem Finite.exists_min [Finite α] [Nonempty α] [LinearOrder β] (f : α → β) :
    ∃ x₀ : α, ∀ x, f x₀ ≤ f x := by cases nonempty_fintype α;
  simpa using exists_min_image univ f univ_nonempty
#align finite.exists_min Finite.exists_min
-/

