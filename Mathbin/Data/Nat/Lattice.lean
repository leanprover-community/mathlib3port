/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov

! This file was ported from Lean 3 source module data.nat.lattice
! leanprover-community/mathlib commit 52fa514ec337dd970d71d8de8d0fd68b455a1e54
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Nat.Interval
import Mathbin.Order.ConditionallyCompleteLattice.Finset

/-!
# Conditionally complete linear order structure on `ℕ`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we

* define a `conditionally_complete_linear_order_bot` structure on `ℕ`;
* prove a few lemmas about `supr`/`infi`/`set.Union`/`set.Inter` and natural numbers.
-/


open Set

namespace Nat

open Classical

noncomputable instance : InfSet ℕ :=
  ⟨fun s => if h : ∃ n, n ∈ s then @Nat.find (fun n => n ∈ s) _ h else 0⟩

noncomputable instance : SupSet ℕ :=
  ⟨fun s => if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n => ∀ a ∈ s, a ≤ n) _ h else 0⟩

#print Nat.sInf_def /-
theorem sInf_def {s : Set ℕ} (h : s.Nonempty) : sInf s = @Nat.find (fun n => n ∈ s) _ h :=
  dif_pos _
#align nat.Inf_def Nat.sInf_def
-/

#print Nat.sSup_def /-
theorem sSup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sSup s = @Nat.find (fun n => ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _
#align nat.Sup_def Nat.sSup_def
-/

#print Set.Infinite.Nat.sSup_eq_zero /-
theorem Set.Infinite.Nat.sSup_eq_zero {s : Set ℕ} (h : s.Infinite) : sSup s = 0 :=
  dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_gt n
    (hn k hks).not_lt hk
#align set.infinite.nat.Sup_eq_zero Set.Infinite.Nat.sSup_eq_zero
-/

#print Nat.sInf_eq_zero /-
@[simp]
theorem sInf_eq_zero {s : Set ℕ} : sInf s = 0 ↔ 0 ∈ s ∨ s = ∅ :=
  by
  cases eq_empty_or_nonempty s
  · subst h;
    simp only [or_true_iff, eq_self_iff_true, iff_true_iff, Inf, InfSet.sInf, mem_empty_iff_false,
      exists_false, dif_neg, not_false_iff]
  · simp only [h.ne_empty, or_false_iff, Nat.sInf_def, h, Nat.find_eq_zero]
#align nat.Inf_eq_zero Nat.sInf_eq_zero
-/

#print Nat.sInf_empty /-
@[simp]
theorem sInf_empty : sInf ∅ = 0 := by rw [Inf_eq_zero]; right; rfl
#align nat.Inf_empty Nat.sInf_empty
-/

#print Nat.iInf_of_empty /-
@[simp]
theorem iInf_of_empty {ι : Sort _} [IsEmpty ι] (f : ι → ℕ) : iInf f = 0 := by
  rw [iInf_of_empty', sInf_empty]
#align nat.infi_of_empty Nat.iInf_of_empty
-/

#print Nat.sInf_mem /-
theorem sInf_mem {s : Set ℕ} (h : s.Nonempty) : sInf s ∈ s := by rw [Nat.sInf_def h];
  exact Nat.find_spec h
#align nat.Inf_mem Nat.sInf_mem
-/

#print Nat.not_mem_of_lt_sInf /-
theorem not_mem_of_lt_sInf {s : Set ℕ} {m : ℕ} (hm : m < sInf s) : m ∉ s :=
  by
  cases eq_empty_or_nonempty s
  · subst h; apply not_mem_empty
  · rw [Nat.sInf_def h] at hm; exact Nat.find_min h hm
#align nat.not_mem_of_lt_Inf Nat.not_mem_of_lt_sInf
-/

#print Nat.sInf_le /-
protected theorem sInf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : sInf s ≤ m := by
  rw [Nat.sInf_def ⟨m, hm⟩]; exact Nat.find_min' ⟨m, hm⟩ hm
#align nat.Inf_le Nat.sInf_le
-/

#print Nat.nonempty_of_pos_sInf /-
theorem nonempty_of_pos_sInf {s : Set ℕ} (h : 0 < sInf s) : s.Nonempty :=
  by
  by_contra contra; rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : Inf s ≠ 0 := ne_of_gt h; apply h'
  rw [Nat.sInf_eq_zero]; right; assumption
#align nat.nonempty_of_pos_Inf Nat.nonempty_of_pos_sInf
-/

#print Nat.nonempty_of_sInf_eq_succ /-
theorem nonempty_of_sInf_eq_succ {s : Set ℕ} {k : ℕ} (h : sInf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_sInf (h.symm ▸ succ_pos k : sInf s > 0)
#align nat.nonempty_of_Inf_eq_succ Nat.nonempty_of_sInf_eq_succ
-/

#print Nat.eq_Ici_of_nonempty_of_upward_closed /-
theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = Ici (sInf s) :=
  ext fun n => ⟨fun H => Nat.sInf_le H, fun H => hs' (sInf s) n H (sInf_mem hs)⟩
#align nat.eq_Ici_of_nonempty_of_upward_closed Nat.eq_Ici_of_nonempty_of_upward_closed
-/

#print Nat.sInf_upward_closed_eq_succ_iff /-
theorem sInf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : sInf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s :=
  by
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_Inf_eq_succ H) hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩
  · rintro ⟨H, H'⟩
    rw [Inf_def (⟨_, H⟩ : s.nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns => H' <| hs n k (lt_succ_iff.mp hnk) hns⟩
#align nat.Inf_upward_closed_eq_succ_iff Nat.sInf_upward_closed_eq_succ_iff
-/

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with
    sSup := sSup
    sInf := sInf
    le_cSup := fun s a hb ha => by rw [Sup_def hb] <;> revert a ha <;> exact @Nat.find_spec _ _ hb
    cSup_le := fun s a hs ha => by rw [Sup_def ⟨a, ha⟩] <;> exact Nat.find_min' _ ha
    le_cInf := fun s a hs hb => by
      rw [Inf_def hs] <;> exact hb (@Nat.find_spec (fun n => n ∈ s) _ _)
    cInf_le := fun s a hb ha => by rw [Inf_def ⟨a, ha⟩] <;> exact Nat.find_min' _ ha
    csSup_empty :=
      by
      simp only [Sup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial }

#print Nat.sSup_mem /-
theorem sSup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sSup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.cSup_mem ((finite_le_nat k).Subset hk)
#align nat.Sup_mem Nat.sSup_mem
-/

#print Nat.sInf_add /-
theorem sInf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ sInf { m | p m }) :
    sInf { m | p (m + n) } + n = sInf { m | p m } :=
  by
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.sInf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (Inf { m | p m } - n + n)
    · exact (h.subset hp).elim
    rw [tsub_add_cancel_of_le hn]
    exact csInf_mem (nonempty_of_pos_Inf <| n.zero_le.trans_lt hnp)
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.sInf_def ⟨m, hm⟩, Nat.sInf_def hp]
    rw [Nat.sInf_def hp] at hn
    exact find_add hn
#align nat.Inf_add Nat.sInf_add
-/

#print Nat.sInf_add' /-
theorem sInf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < sInf { m | p m }) :
    sInf { m | p m } + n = sInf { m | p (m - n) } :=
  by
  convert sInf_add _
  · simp_rw [add_tsub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_Inf h
  refine'
    le_csInf ⟨m + n, _⟩ fun b hb =>
      le_of_not_lt fun hbn =>
        ne_of_mem_of_not_mem _ (not_mem_of_lt_Inf h) (tsub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [add_tsub_cancel_right]
  · exact hb
#align nat.Inf_add' Nat.sInf_add'
-/

section

variable {α : Type _} [CompleteLattice α]

/- warning: nat.supr_lt_succ -> Nat.iSup_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u k))) (u n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u k))) (u n))
Case conversion may be inaccurate. Consider using '#align nat.supr_lt_succ Nat.iSup_lt_succₓ'. -/
theorem iSup_lt_succ (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = (⨆ k < n, u k) ⊔ u n := by
  simp [Nat.lt_succ_iff_lt_or_eq, iSup_or, iSup_sup_eq]
#align nat.supr_lt_succ Nat.iSup_lt_succ

/- warning: nat.supr_lt_succ' -> Nat.iSup_lt_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Sup.sup.{u1} α (SemilatticeSup.toHasSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toHasSup.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Sup.sup.{u1} α (SemilatticeSup.toSup.{u1} α (Lattice.toSemilatticeSup.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (iSup.{u1, 1} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iSup.{u1, 0} α (ConditionallyCompleteLattice.toSupSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align nat.supr_lt_succ' Nat.iSup_lt_succ'ₓ'. -/
theorem iSup_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_iSup_nat_succ]; simp
#align nat.supr_lt_succ' Nat.iSup_lt_succ'

/- warning: nat.infi_lt_succ -> Nat.iInf_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u k))) (u n))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u k))) (u n))
Case conversion may be inaccurate. Consider using '#align nat.infi_lt_succ Nat.iInf_lt_succₓ'. -/
theorem iInf_lt_succ (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = (⨅ k < n, u k) ⊓ u n :=
  @iSup_lt_succ αᵒᵈ _ _ _
#align nat.infi_lt_succ Nat.iInf_lt_succ

/- warning: nat.infi_lt_succ' -> Nat.iInf_lt_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Inf.inf.{u1} α (SemilatticeInf.toHasInf.{u1} α (Lattice.toSemilatticeInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)))) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toHasInf.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : CompleteLattice.{u1} α] (u : Nat -> α) (n : Nat), Eq.{succ u1} α (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Inf.inf.{u1} α (Lattice.toInf.{u1} α (ConditionallyCompleteLattice.toLattice.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1))) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (iInf.{u1, 1} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) Nat (fun (k : Nat) => iInf.{u1, 0} α (ConditionallyCompleteLattice.toInfSet.{u1} α (CompleteLattice.toConditionallyCompleteLattice.{u1} α _inst_1)) (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align nat.infi_lt_succ' Nat.iInf_lt_succ'ₓ'. -/
theorem iInf_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @iSup_lt_succ' αᵒᵈ _ _ _
#align nat.infi_lt_succ' Nat.iInf_lt_succ'

end

end Nat

namespace Set

variable {α : Type _}

/- warning: set.bUnion_lt_succ -> Set.biUnion_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u k))) (u n))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u k))) (u n))
Case conversion may be inaccurate. Consider using '#align set.bUnion_lt_succ Set.biUnion_lt_succₓ'. -/
theorem biUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = (⋃ k < n, u k) ∪ u n :=
  Nat.iSup_lt_succ u n
#align set.bUnion_lt_succ Set.biUnion_lt_succ

/- warning: set.bUnion_lt_succ' -> Set.biUnion_lt_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Union.union.{u1} (Set.{u1} α) (Set.hasUnion.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Union.union.{u1} (Set.{u1} α) (Set.instUnionSet.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Set.iUnion.{u1, 1} α Nat (fun (k : Nat) => Set.iUnion.{u1, 0} α (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align set.bUnion_lt_succ' Set.biUnion_lt_succ'ₓ'. -/
theorem biUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.iSup_lt_succ' u n
#align set.bUnion_lt_succ' Set.biUnion_lt_succ'

/- warning: set.bInter_lt_succ -> Set.biInter_lt_succ is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u k))) (u n))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u k))) (u n))
Case conversion may be inaccurate. Consider using '#align set.bInter_lt_succ Set.biInter_lt_succₓ'. -/
theorem biInter_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = (⋂ k < n, u k) ∩ u n :=
  Nat.iInf_lt_succ u n
#align set.bInter_lt_succ Set.biInter_lt_succ

/- warning: set.bInter_lt_succ' -> Set.biInter_lt_succ' is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) (fun (H : LT.lt.{0} Nat Nat.hasLt k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) => u k))) (Inter.inter.{u1} (Set.{u1} α) (Set.hasInter.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat Nat.hasLt k n) (fun (H : LT.lt.{0} Nat Nat.hasLt k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) k (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {α : Type.{u1}} (u : Nat -> (Set.{u1} α)) (n : Nat), Eq.{succ u1} (Set.{u1} α) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) (fun (H : LT.lt.{0} Nat instLTNat k (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) => u k))) (Inter.inter.{u1} (Set.{u1} α) (Set.instInterSet.{u1} α) (u (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) (Set.iInter.{u1, 1} α Nat (fun (k : Nat) => Set.iInter.{u1, 0} α (LT.lt.{0} Nat instLTNat k n) (fun (H : LT.lt.{0} Nat instLTNat k n) => u (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) k (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align set.bInter_lt_succ' Set.biInter_lt_succ'ₓ'. -/
theorem biInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.iInf_lt_succ' u n
#align set.bInter_lt_succ' Set.biInter_lt_succ'

end Set

