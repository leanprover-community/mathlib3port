/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.fintype.powerset
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Finset.Powerset

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

#print Finset.mem_powerset_len_univ_iff /-
theorem Finset.mem_powerset_len_univ_iff [Fintype α] {s : Finset α} {k : ℕ} :
    s ∈ powersetLen k (univ : Finset α) ↔ card s = k :=
  mem_powersetLen.trans <| and_iff_right <| subset_univ _
#align finset.mem_powerset_len_univ_iff Finset.mem_powerset_len_univ_iff
-/

/- warning: finset.univ_filter_card_eq -> Finset.univ_filter_card_eq is a dubious translation:
lean 3 declaration is
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α] (k : Nat), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.filter.{u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k) (fun (a : Finset.{u1} α) => Nat.decidableEq (Finset.card.{u1} α a) k) (Finset.univ.{u1} (Finset.{u1} α) (Finset.fintype.{u1} α _inst_1))) (Finset.powersetLen.{u1} α k (Finset.univ.{u1} α _inst_1))
but is expected to have type
  forall (α : Type.{u1}) [_inst_1 : Fintype.{u1} α] (k : Nat), Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.filter.{u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k) (fun (a : Finset.{u1} α) => instDecidableEqNat (Finset.card.{u1} α a) k) (Finset.univ.{u1} (Finset.{u1} α) (Finset.fintype.{u1} α _inst_1))) (Finset.powersetLen.{u1} α k (Finset.univ.{u1} α _inst_1))
Case conversion may be inaccurate. Consider using '#align finset.univ_filter_card_eq Finset.univ_filter_card_eqₓ'. -/
@[simp]
theorem Finset.univ_filter_card_eq (α : Type _) [Fintype α] (k : ℕ) :
    ((Finset.univ : Finset (Finset α)).filterₓ fun s => s.card = k) = Finset.univ.powersetLen k :=
  by
  ext
  simp [Finset.mem_powersetLen]
#align finset.univ_filter_card_eq Finset.univ_filter_card_eq

/- warning: fintype.card_finset_len -> Fintype.card_finset_len is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (k : Nat), Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k)) (Subtype.fintype.{u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k) (fun (a : Finset.{u1} α) => Nat.decidableEq (Finset.card.{u1} α a) k) (Finset.fintype.{u1} α _inst_1))) (Nat.choose (Fintype.card.{u1} α _inst_1) k)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : Fintype.{u1} α] (k : Nat), Eq.{1} Nat (Fintype.card.{u1} (Subtype.{succ u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k)) (Subtype.fintype.{u1} (Finset.{u1} α) (fun (s : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α s) k) (fun (a : Finset.{u1} α) => instDecidableEqNat (Finset.card.{u1} α a) k) (Finset.fintype.{u1} α _inst_1))) (Nat.choose (Fintype.card.{u1} α _inst_1) k)
Case conversion may be inaccurate. Consider using '#align fintype.card_finset_len Fintype.card_finset_lenₓ'. -/
@[simp]
theorem Fintype.card_finset_len [Fintype α] (k : ℕ) :
    Fintype.card { s : Finset α // s.card = k } = Nat.choose (Fintype.card α) k := by
  simp [Fintype.subtype_card, Finset.card_univ]
#align fintype.card_finset_len Fintype.card_finset_len

#print Set.fintype /-
instance Set.fintype [Fintype α] : Fintype (Set α) :=
  ⟨(@Finset.univ α _).powerset.map ⟨coe, coe_injective⟩, fun s => by
    classical
      refine' mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩
      apply (coe_filter _ _).trans
      rw [coe_univ, Set.sep_univ]
      rfl⟩
#align set.fintype Set.fintype
-/

#print Set.finite' /-
-- Not to be confused with `set.finite`, the predicate
instance Set.finite' [Finite α] : Finite (Set α) :=
  by
  cases nonempty_fintype α
  infer_instance
#align set.finite' Set.finite'
-/

#print Fintype.card_set /-
@[simp]
theorem Fintype.card_set [Fintype α] : Fintype.card (Set α) = 2 ^ Fintype.card α :=
  (Finset.card_map _).trans (Finset.card_powerset _)
#align fintype.card_set Fintype.card_set
-/

