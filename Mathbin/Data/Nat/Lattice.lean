/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Floris van Doorn, Gabriel Ebner, Yury Kudryashov

! This file was ported from Lean 3 source module data.nat.lattice
! leanprover-community/mathlib commit d012cd09a9b256d870751284dd6a29882b0be105
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.ConditionallyCompleteLattice.Finset

/-!
# Conditionally complete linear order structure on `ℕ`

In this file we

* define a `conditionally_complete_linear_order_bot` structure on `ℕ`;
* prove a few lemmas about `supr`/`infi`/`set.Union`/`set.Inter` and natural numbers.
-/


open Set

namespace Nat

open Classical

noncomputable instance : HasInf ℕ :=
  ⟨fun s => if h : ∃ n, n ∈ s then @Nat.find (fun n => n ∈ s) _ h else 0⟩

noncomputable instance : HasSup ℕ :=
  ⟨fun s => if h : ∃ n, ∀ a ∈ s, a ≤ n then @Nat.find (fun n => ∀ a ∈ s, a ≤ n) _ h else 0⟩

theorem Inf_def {s : Set ℕ} (h : s.Nonempty) : inf s = @Nat.find (fun n => n ∈ s) _ h :=
  dif_pos _
#align nat.Inf_def Nat.Inf_def

theorem Sup_def {s : Set ℕ} (h : ∃ n, ∀ a ∈ s, a ≤ n) :
    sup s = @Nat.find (fun n => ∀ a ∈ s, a ≤ n) _ h :=
  dif_pos _
#align nat.Sup_def Nat.Sup_def

theorem Set.Infinite.Nat.Sup_eq_zero {s : Set ℕ} (h : s.Infinite) : sup s = 0 :=
  dif_neg fun ⟨n, hn⟩ =>
    let ⟨k, hks, hk⟩ := h.exists_nat_lt n
    (hn k hks).not_lt hk
#align set.infinite.nat.Sup_eq_zero Set.Infinite.Nat.Sup_eq_zero

@[simp]
theorem Inf_eq_zero {s : Set ℕ} : inf s = 0 ↔ 0 ∈ s ∨ s = ∅ := by
  cases eq_empty_or_nonempty s
  · subst h
    simp only [or_true_iff, eq_self_iff_true, iff_true_iff, Inf, HasInf.inf, mem_empty_iff_false,
      exists_false, dif_neg, not_false_iff]
  · simp only [h.ne_empty, or_false_iff, Nat.Inf_def, h, Nat.find_eq_zero]
#align nat.Inf_eq_zero Nat.Inf_eq_zero

@[simp]
theorem Inf_empty : inf ∅ = 0 := by 
  rw [Inf_eq_zero]
  right
  rfl
#align nat.Inf_empty Nat.Inf_empty

@[simp]
theorem infi_of_empty {ι : Sort _} [IsEmpty ι] (f : ι → ℕ) : infi f = 0 := by
  rw [infi_of_empty', Inf_empty]
#align nat.infi_of_empty Nat.infi_of_empty

theorem Inf_mem {s : Set ℕ} (h : s.Nonempty) : inf s ∈ s := by
  rw [Nat.Inf_def h]
  exact Nat.find_spec h
#align nat.Inf_mem Nat.Inf_mem

theorem not_mem_of_lt_Inf {s : Set ℕ} {m : ℕ} (hm : m < inf s) : m ∉ s := by
  cases eq_empty_or_nonempty s
  · subst h
    apply not_mem_empty
  · rw [Nat.Inf_def h] at hm
    exact Nat.find_min h hm
#align nat.not_mem_of_lt_Inf Nat.not_mem_of_lt_Inf

protected theorem Inf_le {s : Set ℕ} {m : ℕ} (hm : m ∈ s) : inf s ≤ m := by
  rw [Nat.Inf_def ⟨m, hm⟩]
  exact Nat.find_min' ⟨m, hm⟩ hm
#align nat.Inf_le Nat.Inf_le

theorem nonempty_of_pos_Inf {s : Set ℕ} (h : 0 < inf s) : s.Nonempty := by
  by_contra contra
  rw [Set.not_nonempty_iff_eq_empty] at contra
  have h' : Inf s ≠ 0 := ne_of_gt h
  apply h'
  rw [Nat.Inf_eq_zero]
  right
  assumption
#align nat.nonempty_of_pos_Inf Nat.nonempty_of_pos_Inf

theorem nonempty_of_Inf_eq_succ {s : Set ℕ} {k : ℕ} (h : inf s = k + 1) : s.Nonempty :=
  nonempty_of_pos_Inf (h.symm ▸ succ_pos k : inf s > 0)
#align nat.nonempty_of_Inf_eq_succ Nat.nonempty_of_Inf_eq_succ

theorem eq_Ici_of_nonempty_of_upward_closed {s : Set ℕ} (hs : s.Nonempty)
    (hs' : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s) : s = ici (inf s) :=
  ext fun n => ⟨fun H => Nat.Inf_le H, fun H => hs' (inf s) n H (Inf_mem hs)⟩
#align nat.eq_Ici_of_nonempty_of_upward_closed Nat.eq_Ici_of_nonempty_of_upward_closed

theorem Inf_upward_closed_eq_succ_iff {s : Set ℕ} (hs : ∀ k₁ k₂ : ℕ, k₁ ≤ k₂ → k₁ ∈ s → k₂ ∈ s)
    (k : ℕ) : inf s = k + 1 ↔ k + 1 ∈ s ∧ k ∉ s := by
  constructor
  · intro H
    rw [eq_Ici_of_nonempty_of_upward_closed (nonempty_of_Inf_eq_succ H) hs, H, mem_Ici, mem_Ici]
    exact ⟨le_rfl, k.not_succ_le_self⟩
  · rintro ⟨H, H'⟩
    rw [Inf_def (⟨_, H⟩ : s.nonempty), find_eq_iff]
    exact ⟨H, fun n hnk hns => H' <| hs n k (lt_succ_iff.mp hnk) hns⟩
#align nat.Inf_upward_closed_eq_succ_iff Nat.Inf_upward_closed_eq_succ_iff

/-- This instance is necessary, otherwise the lattice operations would be derived via
conditionally_complete_linear_order_bot and marked as noncomputable. -/
instance : Lattice ℕ :=
  LinearOrder.toLattice

noncomputable instance : ConditionallyCompleteLinearOrderBot ℕ :=
  { (inferInstance : OrderBot ℕ), (LinearOrder.toLattice : Lattice ℕ),
    (inferInstance : LinearOrder ℕ) with 
    sup := sup
    inf := inf
    le_cSup := fun s a hb ha => by rw [Sup_def hb] <;> revert a ha <;> exact @Nat.find_spec _ _ hb
    cSup_le := fun s a hs ha => by rw [Sup_def ⟨a, ha⟩] <;> exact Nat.find_min' _ ha
    le_cInf := fun s a hs hb => by
      rw [Inf_def hs] <;> exact hb (@Nat.find_spec (fun n => n ∈ s) _ _)
    cInf_le := fun s a hb ha => by rw [Inf_def ⟨a, ha⟩] <;> exact Nat.find_min' _ ha
    cSup_empty := by
      simp only [Sup_def, Set.mem_empty_iff_false, forall_const, forall_prop_of_false,
        not_false_iff, exists_const]
      apply bot_unique (Nat.find_min' _ _)
      trivial }

theorem Sup_mem {s : Set ℕ} (h₁ : s.Nonempty) (h₂ : BddAbove s) : sup s ∈ s :=
  let ⟨k, hk⟩ := h₂
  h₁.cSup_mem ((finite_le_nat k).Subset hk)
#align nat.Sup_mem Nat.Sup_mem

theorem Inf_add {n : ℕ} {p : ℕ → Prop} (hn : n ≤ inf { m | p m }) :
    inf { m | p (m + n) } + n = inf { m | p m } := by
  obtain h | ⟨m, hm⟩ := { m | p (m + n) }.eq_empty_or_nonempty
  · rw [h, Nat.Inf_empty, zero_add]
    obtain hnp | hnp := hn.eq_or_lt
    · exact hnp
    suffices hp : p (Inf { m | p m } - n + n)
    · exact (h.subset hp).elim
    rw [tsub_add_cancel_of_le hn]
    exact Inf_mem (nonempty_of_pos_Inf <| n.zero_le.trans_lt hnp)
  · have hp : ∃ n, n ∈ { m | p m } := ⟨_, hm⟩
    rw [Nat.Inf_def ⟨m, hm⟩, Nat.Inf_def hp]
    rw [Nat.Inf_def hp] at hn
    exact find_add hn
#align nat.Inf_add Nat.Inf_add

theorem Inf_add' {n : ℕ} {p : ℕ → Prop} (h : 0 < inf { m | p m }) :
    inf { m | p m } + n = inf { m | p (m - n) } := by
  convert Inf_add _
  · simp_rw [add_tsub_cancel_right]
  obtain ⟨m, hm⟩ := nonempty_of_pos_Inf h
  refine'
    le_cInf ⟨m + n, _⟩ fun b hb =>
      le_of_not_lt fun hbn =>
        ne_of_mem_of_not_mem _ (not_mem_of_lt_Inf h) (tsub_eq_zero_of_le hbn.le)
  · dsimp
    rwa [add_tsub_cancel_right]
  · exact hb
#align nat.Inf_add' Nat.Inf_add'

section

variable {α : Type _} [CompleteLattice α]

theorem supr_lt_succ (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = (⨆ k < n, u k) ⊔ u n := by
  simp [Nat.lt_succ_iff_lt_or_eq, supr_or, supr_sup_eq]
#align nat.supr_lt_succ Nat.supr_lt_succ

theorem supr_lt_succ' (u : ℕ → α) (n : ℕ) : (⨆ k < n + 1, u k) = u 0 ⊔ ⨆ k < n, u (k + 1) := by
  rw [← sup_supr_nat_succ]
  simp
#align nat.supr_lt_succ' Nat.supr_lt_succ'

theorem infi_lt_succ (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = (⨅ k < n, u k) ⊓ u n :=
  @supr_lt_succ αᵒᵈ _ _ _
#align nat.infi_lt_succ Nat.infi_lt_succ

theorem infi_lt_succ' (u : ℕ → α) (n : ℕ) : (⨅ k < n + 1, u k) = u 0 ⊓ ⨅ k < n, u (k + 1) :=
  @supr_lt_succ' αᵒᵈ _ _ _
#align nat.infi_lt_succ' Nat.infi_lt_succ'

end

end Nat

namespace Set

variable {α : Type _}

theorem bUnion_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = (⋃ k < n, u k) ∪ u n :=
  Nat.supr_lt_succ u n
#align set.bUnion_lt_succ Set.bUnion_lt_succ

theorem bUnion_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋃ k < n + 1, u k) = u 0 ∪ ⋃ k < n, u (k + 1) :=
  Nat.supr_lt_succ' u n
#align set.bUnion_lt_succ' Set.bUnion_lt_succ'

theorem bInter_lt_succ (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = (⋂ k < n, u k) ∩ u n :=
  Nat.infi_lt_succ u n
#align set.bInter_lt_succ Set.bInter_lt_succ

theorem bInter_lt_succ' (u : ℕ → Set α) (n : ℕ) : (⋂ k < n + 1, u k) = u 0 ∩ ⋂ k < n, u (k + 1) :=
  Nat.infi_lt_succ' u n
#align set.bInter_lt_succ' Set.bInter_lt_succ'

end Set

