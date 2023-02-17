/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.finset.powerset
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Finset.Lattice
import Mathbin.Data.Multiset.Powerset

/-!
# The powerset of a finset

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/


namespace Finset

open Function Multiset

variable {α : Type _} {s t : Finset α}

/-! ### powerset -/


section Powerset

#print Finset.powerset /-
/-- When `s` is a finset, `s.powerset` is the finset of all subsets of `s` (seen as finsets). -/
def powerset (s : Finset α) : Finset (Finset α) :=
  ⟨s.1.powerset.pmap Finset.mk fun t h => nodup_of_le (mem_powerset.1 h) s.Nodup,
    s.Nodup.powerset.pmap fun a ha b hb => congr_arg Finset.val⟩
#align finset.powerset Finset.powerset
-/

#print Finset.mem_powerset /-
@[simp]
theorem mem_powerset {s t : Finset α} : s ∈ powerset t ↔ s ⊆ t := by
  cases s <;> simp only [powerset, mem_mk, mem_pmap, mem_powerset, exists_prop, exists_eq_right] <;>
    rw [← val_le_iff]
#align finset.mem_powerset Finset.mem_powerset
-/

#print Finset.coe_powerset /-
@[simp, norm_cast]
theorem coe_powerset (s : Finset α) :
    (s.powerset : Set (Finset α)) = coe ⁻¹' (s : Set α).powerset :=
  by
  ext
  simp
#align finset.coe_powerset Finset.coe_powerset
-/

#print Finset.empty_mem_powerset /-
@[simp]
theorem empty_mem_powerset (s : Finset α) : ∅ ∈ powerset s :=
  mem_powerset.2 (empty_subset _)
#align finset.empty_mem_powerset Finset.empty_mem_powerset
-/

#print Finset.mem_powerset_self /-
@[simp]
theorem mem_powerset_self (s : Finset α) : s ∈ powerset s :=
  mem_powerset.2 Subset.rfl
#align finset.mem_powerset_self Finset.mem_powerset_self
-/

#print Finset.powerset_nonempty /-
theorem powerset_nonempty (s : Finset α) : s.powerset.Nonempty :=
  ⟨∅, empty_mem_powerset _⟩
#align finset.powerset_nonempty Finset.powerset_nonempty
-/

#print Finset.powerset_mono /-
@[simp]
theorem powerset_mono {s t : Finset α} : powerset s ⊆ powerset t ↔ s ⊆ t :=
  ⟨fun h => mem_powerset.1 <| h <| mem_powerset_self _, fun st u h =>
    mem_powerset.2 <| Subset.trans (mem_powerset.1 h) st⟩
#align finset.powerset_mono Finset.powerset_mono
-/

#print Finset.powerset_injective /-
theorem powerset_injective : Injective (powerset : Finset α → Finset (Finset α)) :=
  injective_of_le_imp_le _ fun s t => powerset_mono.1
#align finset.powerset_injective Finset.powerset_injective
-/

#print Finset.powerset_inj /-
@[simp]
theorem powerset_inj : powerset s = powerset t ↔ s = t :=
  powerset_injective.eq_iff
#align finset.powerset_inj Finset.powerset_inj
-/

#print Finset.powerset_empty /-
@[simp]
theorem powerset_empty : (∅ : Finset α).powerset = {∅} :=
  rfl
#align finset.powerset_empty Finset.powerset_empty
-/

#print Finset.powerset_eq_singleton_empty /-
@[simp]
theorem powerset_eq_singleton_empty : s.powerset = {∅} ↔ s = ∅ := by
  rw [← powerset_empty, powerset_inj]
#align finset.powerset_eq_singleton_empty Finset.powerset_eq_singleton_empty
-/

#print Finset.card_powerset /-
/-- **Number of Subsets of a Set** -/
@[simp]
theorem card_powerset (s : Finset α) : card (powerset s) = 2 ^ card s :=
  (card_pmap _ _ _).trans (card_powerset s.1)
#align finset.card_powerset Finset.card_powerset
-/

#print Finset.not_mem_of_mem_powerset_of_not_mem /-
theorem not_mem_of_mem_powerset_of_not_mem {s t : Finset α} {a : α} (ht : t ∈ s.powerset)
    (h : a ∉ s) : a ∉ t := by
  apply mt _ h
  apply mem_powerset.1 ht
#align finset.not_mem_of_mem_powerset_of_not_mem Finset.not_mem_of_mem_powerset_of_not_mem
-/

#print Finset.powerset_insert /-
theorem powerset_insert [DecidableEq α] (s : Finset α) (a : α) :
    powerset (insert a s) = s.powerset ∪ s.powerset.image (insert a) :=
  by
  ext t
  simp only [exists_prop, mem_powerset, mem_image, mem_union, subset_insert_iff]
  by_cases h : a ∈ t
  · constructor
    · exact fun H => Or.inr ⟨_, H, insert_erase h⟩
    · intro H
      cases H
      · exact subset.trans (erase_subset a t) H
      · rcases H with ⟨u, hu⟩
        rw [← hu.2]
        exact subset.trans (erase_insert_subset a u) hu.1
  · have : ¬∃ u : Finset α, u ⊆ s ∧ insert a u = t := by simp [Ne.symm (ne_insert_of_not_mem _ _ h)]
    simp [Finset.erase_eq_of_not_mem h, this]
#align finset.powerset_insert Finset.powerset_insert
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Finset.decidableExistsOfDecidableSubsets /-
/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for any subset. -/
instance decidableExistsOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∃ (t : _)(h : t ⊆ s), p t h) :=
  decidable_of_iff (∃ (t : _)(hs : t ∈ s.powerset), p t (mem_powerset.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_powerset.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_subsets Finset.decidableExistsOfDecidableSubsets
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print Finset.decidableForallOfDecidableSubsets /-
/-- For predicate `p` decidable on subsets, it is decidable whether `p` holds for every subset. -/
instance decidableForallOfDecidableSubsets {s : Finset α} {p : ∀ (t) (_ : t ⊆ s), Prop}
    [∀ (t) (h : t ⊆ s), Decidable (p t h)] : Decidable (∀ (t) (h : t ⊆ s), p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.powerset), p t (mem_powerset.1 h))
    ⟨fun h t hs => h t (mem_powerset.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_subsets Finset.decidableForallOfDecidableSubsets
-/

#print Finset.decidableExistsOfDecidableSubsets' /-
/-- A version of `finset.decidable_exists_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (h : t ⊆ s), Decidable (p t)) : Decidable (∃ (t : _)(h : t ⊆ s), p t) :=
  @Finset.decidableExistsOfDecidableSubsets _ _ _ hu
#align finset.decidable_exists_of_decidable_subsets' Finset.decidableExistsOfDecidableSubsets'
-/

#print Finset.decidableForallOfDecidableSubsets' /-
/-- A version of `finset.decidable_forall_of_decidable_subsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (h : t ⊆ s), Decidable (p t)) : Decidable (∀ (t) (h : t ⊆ s), p t) :=
  @Finset.decidableForallOfDecidableSubsets _ _ _ hu
#align finset.decidable_forall_of_decidable_subsets' Finset.decidableForallOfDecidableSubsets'
-/

end Powerset

section Ssubsets

variable [DecidableEq α]

#print Finset.ssubsets /-
/-- For `s` a finset, `s.ssubsets` is the finset comprising strict subsets of `s`. -/
def ssubsets (s : Finset α) : Finset (Finset α) :=
  erase (powerset s) s
#align finset.ssubsets Finset.ssubsets
-/

#print Finset.mem_ssubsets /-
@[simp]
theorem mem_ssubsets {s t : Finset α} : t ∈ s.ssubsets ↔ t ⊂ s := by
  rw [ssubsets, mem_erase, mem_powerset, ssubset_iff_subset_ne, and_comm]
#align finset.mem_ssubsets Finset.mem_ssubsets
-/

#print Finset.empty_mem_ssubsets /-
theorem empty_mem_ssubsets {s : Finset α} (h : s.Nonempty) : ∅ ∈ s.ssubsets :=
  by
  rw [mem_ssubsets, ssubset_iff_subset_ne]
  exact ⟨empty_subset s, h.ne_empty.symm⟩
#align finset.empty_mem_ssubsets Finset.empty_mem_ssubsets
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊂ » s) -/
#print Finset.decidableExistsOfDecidableSsubsets /-
/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for any ssubset. -/
instance decidableExistsOfDecidableSsubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∃ t h, p t h) :=
  decidable_of_iff (∃ (t : _)(hs : t ∈ s.ssubsets), p t (mem_ssubsets.1 hs))
    ⟨fun ⟨t, _, hp⟩ => ⟨t, _, hp⟩, fun ⟨t, hs, hp⟩ => ⟨t, mem_ssubsets.2 hs, hp⟩⟩
#align finset.decidable_exists_of_decidable_ssubsets Finset.decidableExistsOfDecidableSsubsets
-/

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (t «expr ⊂ » s) -/
#print Finset.decidableForallOfDecidableSsubsets /-
/-- For predicate `p` decidable on ssubsets, it is decidable whether `p` holds for every ssubset. -/
instance decidableForallOfDecidableSsubsets {s : Finset α} {p : ∀ (t) (_ : t ⊂ s), Prop}
    [∀ (t) (h : t ⊂ s), Decidable (p t h)] : Decidable (∀ t h, p t h) :=
  decidable_of_iff (∀ (t) (h : t ∈ s.ssubsets), p t (mem_ssubsets.1 h))
    ⟨fun h t hs => h t (mem_ssubsets.2 hs), fun h _ _ => h _ _⟩
#align finset.decidable_forall_of_decidable_ssubsets Finset.decidableForallOfDecidableSsubsets
-/

#print Finset.decidableExistsOfDecidableSsubsets' /-
/-- A version of `finset.decidable_exists_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableExistsOfDecidableSsubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (h : t ⊂ s), Decidable (p t)) : Decidable (∃ (t : _)(h : t ⊂ s), p t) :=
  @Finset.decidableExistsOfDecidableSsubsets _ _ _ _ hu
#align finset.decidable_exists_of_decidable_ssubsets' Finset.decidableExistsOfDecidableSsubsets'
-/

#print Finset.decidableForallOfDecidableSsubsets' /-
/-- A version of `finset.decidable_forall_of_decidable_ssubsets` with a non-dependent `p`.
Typeclass inference cannot find `hu` here, so this is not an instance. -/
def decidableForallOfDecidableSsubsets' {s : Finset α} {p : Finset α → Prop}
    (hu : ∀ (t) (h : t ⊂ s), Decidable (p t)) : Decidable (∀ (t) (h : t ⊂ s), p t) :=
  @Finset.decidableForallOfDecidableSsubsets _ _ _ _ hu
#align finset.decidable_forall_of_decidable_ssubsets' Finset.decidableForallOfDecidableSsubsets'
-/

end Ssubsets

section PowersetLen

#print Finset.powersetLen /-
/-- Given an integer `n` and a finset `s`, then `powerset_len n s` is the finset of subsets of `s`
of cardinality `n`. -/
def powersetLen (n : ℕ) (s : Finset α) : Finset (Finset α) :=
  ⟨(s.1.powersetLen n).pmap Finset.mk fun t h => nodup_of_le (mem_powersetLen.1 h).1 s.2,
    s.2.powersetLen.pmap fun a ha b hb => congr_arg Finset.val⟩
#align finset.powerset_len Finset.powersetLen
-/

#print Finset.mem_powersetLen /-
/-- **Formula for the Number of Combinations** -/
theorem mem_powersetLen {n} {s t : Finset α} : s ∈ powersetLen n t ↔ s ⊆ t ∧ card s = n := by
  cases s <;> simp [powerset_len, val_le_iff.symm] <;> rfl
#align finset.mem_powerset_len Finset.mem_powersetLen
-/

#print Finset.powersetLen_mono /-
@[simp]
theorem powersetLen_mono {n} {s t : Finset α} (h : s ⊆ t) : powersetLen n s ⊆ powersetLen n t :=
  fun u h' => mem_powersetLen.2 <| And.imp (fun h₂ => Subset.trans h₂ h) id (mem_powersetLen.1 h')
#align finset.powerset_len_mono Finset.powersetLen_mono
-/

#print Finset.card_powersetLen /-
/-- **Formula for the Number of Combinations** -/
@[simp]
theorem card_powersetLen (n : ℕ) (s : Finset α) : card (powersetLen n s) = Nat.choose (card s) n :=
  (card_pmap _ _ _).trans (card_powersetLen n s.1)
#align finset.card_powerset_len Finset.card_powersetLen
-/

#print Finset.powersetLen_zero /-
@[simp]
theorem powersetLen_zero (s : Finset α) : Finset.powersetLen 0 s = {∅} :=
  by
  ext; rw [mem_powerset_len, mem_singleton, card_eq_zero]
  refine'
    ⟨fun h => h.2, fun h => by
      rw [h]
      exact ⟨empty_subset s, rfl⟩⟩
#align finset.powerset_len_zero Finset.powersetLen_zero
-/

#print Finset.powersetLen_empty /-
@[simp]
theorem powersetLen_empty (n : ℕ) {s : Finset α} (h : s.card < n) : powersetLen n s = ∅ :=
  Finset.card_eq_zero.mp (by rw [card_powerset_len, Nat.choose_eq_zero_of_lt h])
#align finset.powerset_len_empty Finset.powersetLen_empty
-/

/- warning: finset.powerset_len_eq_filter -> Finset.powersetLen_eq_filter is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} {n : Nat} {s : Finset.{u1} α}, Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.powersetLen.{u1} α n s) (Finset.filter.{u1} (Finset.{u1} α) (fun (x : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α x) n) (fun (a : Finset.{u1} α) => Nat.decidableEq (Finset.card.{u1} α a) n) (Finset.powerset.{u1} α s))
but is expected to have type
  forall {α : Type.{u1}} {n : Nat} {s : Finset.{u1} α}, Eq.{succ u1} (Finset.{u1} (Finset.{u1} α)) (Finset.powersetLen.{u1} α n s) (Finset.filter.{u1} (Finset.{u1} α) (fun (x : Finset.{u1} α) => Eq.{1} Nat (Finset.card.{u1} α x) n) (fun (a : Finset.{u1} α) => instDecidableEqNat (Finset.card.{u1} α a) n) (Finset.powerset.{u1} α s))
Case conversion may be inaccurate. Consider using '#align finset.powerset_len_eq_filter Finset.powersetLen_eq_filterₓ'. -/
theorem powersetLen_eq_filter {n} {s : Finset α} :
    powersetLen n s = (powerset s).filterₓ fun x => x.card = n :=
  by
  ext
  simp [mem_powerset_len]
#align finset.powerset_len_eq_filter Finset.powersetLen_eq_filter

#print Finset.powersetLen_succ_insert /-
theorem powersetLen_succ_insert [DecidableEq α] {x : α} {s : Finset α} (h : x ∉ s) (n : ℕ) :
    powersetLen n.succ (insert x s) = powersetLen n.succ s ∪ (powersetLen n s).image (insert x) :=
  by
  rw [powerset_len_eq_filter, powerset_insert, filter_union, ← powerset_len_eq_filter]
  congr
  rw [powerset_len_eq_filter, image_filter]
  congr 1
  ext t
  simp only [mem_powerset, mem_filter, Function.comp_apply, and_congr_right_iff]
  intro ht
  have : x ∉ t := fun H => h (ht H)
  simp [card_insert_of_not_mem this, Nat.succ_inj']
#align finset.powerset_len_succ_insert Finset.powersetLen_succ_insert
-/

#print Finset.powersetLen_nonempty /-
theorem powersetLen_nonempty {n : ℕ} {s : Finset α} (h : n ≤ s.card) : (powersetLen n s).Nonempty :=
  by
  classical
    induction' s using Finset.induction_on with x s hx IH generalizing n
    · rw [card_empty, le_zero_iff] at h
      rw [h, powerset_len_zero]
      exact Finset.singleton_nonempty _
    · cases n
      · simp
      · rw [card_insert_of_not_mem hx, Nat.succ_le_succ_iff] at h
        rw [powerset_len_succ_insert hx]
        refine' nonempty.mono _ ((IH h).image (insert x))
        convert subset_union_right _ _
#align finset.powerset_len_nonempty Finset.powersetLen_nonempty
-/

#print Finset.powersetLen_self /-
@[simp]
theorem powersetLen_self (s : Finset α) : powersetLen s.card s = {s} :=
  by
  ext
  rw [mem_powerset_len, mem_singleton]
  constructor
  · exact fun ⟨hs, hc⟩ => eq_of_subset_of_card_le hs hc.ge
  · rintro rfl
    simp
#align finset.powerset_len_self Finset.powersetLen_self
-/

/- warning: finset.pairwise_disjoint_powerset_len -> Finset.pairwise_disjoint_powersetLen is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} (s : Finset.{u1} α), Pairwise.{0} Nat (fun (i : Nat) (j : Nat) => Disjoint.{u1} (Finset.{u1} (Finset.{u1} α)) (Finset.partialOrder.{u1} (Finset.{u1} α)) (Finset.orderBot.{u1} (Finset.{u1} α)) (Finset.powersetLen.{u1} α i s) (Finset.powersetLen.{u1} α j s))
but is expected to have type
  forall {α : Type.{u1}} (s : Finset.{u1} α), Pairwise.{0} Nat (fun (i : Nat) (j : Nat) => Disjoint.{u1} (Finset.{u1} (Finset.{u1} α)) (Finset.partialOrder.{u1} (Finset.{u1} α)) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} (Finset.{u1} α)) (Finset.powersetLen.{u1} α i s) (Finset.powersetLen.{u1} α j s))
Case conversion may be inaccurate. Consider using '#align finset.pairwise_disjoint_powerset_len Finset.pairwise_disjoint_powersetLenₓ'. -/
theorem pairwise_disjoint_powersetLen (s : Finset α) :
    Pairwise fun i j => Disjoint (s.powersetLen i) (s.powersetLen j) := fun i j hij =>
  Finset.disjoint_left.mpr fun x hi hj =>
    hij <| (mem_powersetLen.mp hi).2.symm.trans (mem_powersetLen.mp hj).2
#align finset.pairwise_disjoint_powerset_len Finset.pairwise_disjoint_powersetLen

#print Finset.powerset_card_disjUnionᵢ /-
theorem powerset_card_disjUnionᵢ (s : Finset α) :
    Finset.powerset s =
      (range (s.card + 1)).disjUnionₓ (fun i => powersetLen i s)
        (s.pairwise_disjoint_powersetLen.set_pairwise _) :=
  by
  refine' ext fun a => ⟨fun ha => _, fun ha => _⟩
  · rw [mem_disj_Union]
    exact
      ⟨a.card, mem_range.mpr (Nat.lt_succ_of_le (card_le_of_subset (mem_powerset.mp ha))),
        mem_powerset_len.mpr ⟨mem_powerset.mp ha, rfl⟩⟩
  · rcases mem_disj_Union.mp ha with ⟨i, hi, ha⟩
    exact mem_powerset.mpr (mem_powerset_len.mp ha).1
#align finset.powerset_card_disj_Union Finset.powerset_card_disjUnionᵢ
-/

#print Finset.powerset_card_bunionᵢ /-
theorem powerset_card_bunionᵢ [DecidableEq (Finset α)] (s : Finset α) :
    Finset.powerset s = (range (s.card + 1)).bunionᵢ fun i => powersetLen i s := by
  simpa only [disj_Union_eq_bUnion] using powerset_card_disj_Union s
#align finset.powerset_card_bUnion Finset.powerset_card_bunionᵢ
-/

/- warning: finset.powerset_len_sup -> Finset.powerset_len_sup is a dubious translation:
lean 3 declaration is
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (u : Finset.{u1} α) (n : Nat), (LT.lt.{0} Nat Nat.hasLt n (Finset.card.{u1} α u)) -> (Eq.{succ u1} (Finset.{u1} α) (Finset.sup.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.lattice.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.orderBot.{u1} α) (Finset.powersetLen.{u1} α (Nat.succ n) u) (id.{succ u1} (Finset.{u1} α))) u)
but is expected to have type
  forall {α : Type.{u1}} [_inst_1 : DecidableEq.{succ u1} α] (u : Finset.{u1} α) (n : Nat), (LT.lt.{0} Nat instLTNat n (Finset.card.{u1} α u)) -> (Eq.{succ u1} (Finset.{u1} α) (Finset.sup.{u1, u1} (Finset.{u1} α) (Finset.{u1} α) (Lattice.toSemilatticeSup.{u1} (Finset.{u1} α) (Finset.instLatticeFinset.{u1} α (fun (a : α) (b : α) => _inst_1 a b))) (Finset.instOrderBotFinsetToLEToPreorderPartialOrder.{u1} α) (Finset.powersetLen.{u1} α (Nat.succ n) u) (id.{succ u1} (Finset.{u1} α))) u)
Case conversion may be inaccurate. Consider using '#align finset.powerset_len_sup Finset.powerset_len_supₓ'. -/
theorem powerset_len_sup [DecidableEq α] (u : Finset α) (n : ℕ) (hn : n < u.card) :
    (powersetLen n.succ u).sup id = u := by
  apply le_antisymm
  · simp_rw [Finset.sup_le_iff, mem_powerset_len]
    rintro x ⟨h, -⟩
    exact h
  · rw [sup_eq_bUnion, le_iff_subset, subset_iff]
    cases' (Nat.succ_le_of_lt hn).eq_or_lt with h' h'
    · simp [h']
    · intro x hx
      simp only [mem_bUnion, exists_prop, id.def]
      obtain ⟨t, ht⟩ : ∃ t, t ∈ powerset_len n (u.erase x) := powerset_len_nonempty _
      · refine' ⟨insert x t, _, mem_insert_self _ _⟩
        rw [← insert_erase hx, powerset_len_succ_insert (not_mem_erase _ _)]
        exact mem_union_right _ (mem_image_of_mem _ ht)
      · rw [card_erase_of_mem hx]
        exact Nat.le_pred_of_lt hn
#align finset.powerset_len_sup Finset.powerset_len_sup

#print Finset.powersetLen_card_add /-
@[simp]
theorem powersetLen_card_add (s : Finset α) {i : ℕ} (hi : 0 < i) : s.powersetLen (s.card + i) = ∅ :=
  Finset.powersetLen_empty _ (lt_add_of_pos_right (Finset.card s) hi)
#align finset.powerset_len_card_add Finset.powersetLen_card_add
-/

#print Finset.map_val_val_powersetLen /-
@[simp]
theorem map_val_val_powersetLen (s : Finset α) (i : ℕ) :
    (s.powersetLen i).val.map Finset.val = s.1.powersetLen i := by
  simp [Finset.powersetLen, map_pmap, pmap_eq_map, map_id']
#align finset.map_val_val_powerset_len Finset.map_val_val_powersetLen
-/

#print Finset.powersetLen_map /-
theorem powersetLen_map {β : Type _} (f : α ↪ β) (n : ℕ) (s : Finset α) :
    powersetLen n (s.map f) = (powersetLen n s).map (mapEmbedding f).toEmbedding :=
  eq_of_veq <|
    Multiset.map_injective (@eq_of_veq _) <| by
      simp_rw [map_val_val_powerset_len, map_val, Multiset.map_map, Function.comp,
        RelEmbedding.coeFn_toEmbedding, map_embedding_apply, map_val, ← Multiset.map_map _ val,
        map_val_val_powerset_len, Multiset.powersetLen_map]
#align finset.powerset_len_map Finset.powersetLen_map
-/

end PowersetLen

end Finset

