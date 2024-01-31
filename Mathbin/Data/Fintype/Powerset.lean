/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Data.Fintype.Card
import Data.Finset.Powerset

#align_import data.fintype.powerset from "leanprover-community/mathlib"@"327c3c0d9232d80e250dc8f65e7835b82b266ea5"

/-!
# fintype instance for `set α`, when `α` is a fintype

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


variable {α : Type _}

open Finset

#print Finset.fintype /-
instance Finset.fintype [Fintype α] : Fintype (Finset α) :=
  ⟨univ.powerset, fun x => Finset.mem_powerset.2 (Finset.subset_univ _)⟩
#align finset.fintype Finset.fintype
-/

#print Fintype.card_finset /-
@[simp]
theorem Fintype.card_finset [Fintype α] : Fintype.card (Finset α) = 2 ^ Fintype.card α :=
  Finset.card_powerset Finset.univ
#align fintype.card_finset Fintype.card_finset
-/

#print Finset.powerset_univ /-
@[simp]
theorem Finset.powerset_univ [Fintype α] : (univ : Finset α).powerset = univ :=
  coe_injective <| by simp [-coe_eq_univ]
#align finset.powerset_univ Finset.powerset_univ
-/

#print Finset.powerset_eq_univ /-
@[simp]
theorem Finset.powerset_eq_univ [Fintype α] {s : Finset α} : s.powerset = univ ↔ s = univ := by
  rw [← Finset.powerset_univ, powerset_inj]
#align finset.powerset_eq_univ Finset.powerset_eq_univ
-/

#print Finset.mem_powersetCard_univ /-
theorem Finset.mem_powersetCard_univ [Fintype α] {s : Finset α} {k : ℕ} :
    s ∈ powersetCard k (univ : Finset α) ↔ card s = k :=
  mem_powersetCard.trans <| and_iff_right <| subset_univ _
#align finset.mem_powerset_len_univ_iff Finset.mem_powersetCard_univ
-/

#print Finset.univ_filter_card_eq /-
@[simp]
theorem Finset.univ_filter_card_eq (α : Type _) [Fintype α] (k : ℕ) :
    ((Finset.univ : Finset (Finset α)).filterₓ fun s => s.card = k) = Finset.univ.powersetCard k :=
  by ext; simp [Finset.mem_powersetCard]
#align finset.univ_filter_card_eq Finset.univ_filter_card_eq
-/

#print Fintype.card_finset_len /-
@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]
#align fintype.card_finset_len Fintype.card_finset_len
-/

#print Set.fintype /-
instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).powerset.map ⟨coe, coe_injective⟩, fun s => by classical⟩
#align set.fintype Set.fintype
-/

#print Set.finite' /-
-- Not to be confused with `set.finite`, the predicate
instance Set.finite' [Finite α] : Finite (Set α) := by cases nonempty_fintype α; infer_instance
#align set.finite' Set.finite'
-/

#print Fintype.card_set /-
@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
#align fintype.card_set Fintype.card_set
-/

