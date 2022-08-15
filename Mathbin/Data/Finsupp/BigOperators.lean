/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Data.Finsupp.Basic

/-!

# Sums of collections of finsupp, and their support
This file provides results about the `finsupp.support` of sums of collections of `finsupp`,
including sums of `list`, `multiset`, and `finset`.

The support of the sum is a subset of the union of the supports:
* `list.support_sum_subset`
* `multiset.support_sum_subset`
* `finset.support_sum_subset`

The support of the sum of pairwise disjoint finsupps is equal to the union of the supports
* `list.support_sum_eq`
* `multiset.support_sum_eq`
* `finset.support_sum_eq`

Member in the support of the indexed union over a collection iff
it is a member of the support of a member of the collection:
* `list.mem_foldr_sup_support_iff`
* `multiset.mem_sup_map_support_iff`
* `finset.mem_sup_support_iff`

-/


variable {ι M : Type _} [DecidableEq ι]

theorem List.support_sum_subset [AddMonoidₓ M] (l : List (ι →₀ M)) :
    l.Sum.Support ⊆ l.foldr ((·⊔·) ∘ Finsupp.support) ∅ := by
  induction' l with hd tl IH
  · simp
    
  · simp only [← List.sum_cons, ← List.foldr_cons, ← Finset.union_comm]
    refine' finsupp.support_add.trans (Finset.union_subset_union _ IH)
    rfl
    

theorem Multiset.support_sum_subset [AddCommMonoidₓ M] (s : Multiset (ι →₀ M)) :
    s.Sum.Support ⊆ (s.map Finsupp.support).sup := by
  induction s using Quot.induction_on
  simpa using List.support_sum_subset _

theorem Finset.support_sum_subset [AddCommMonoidₓ M] (s : Finset (ι →₀ M)) :
    (s.Sum id).Support ⊆ Finset.sup s Finsupp.support := by
  classical
  convert Multiset.support_sum_subset s.1 <;> simp

theorem List.mem_foldr_sup_support_iff [Zero M] {l : List (ι →₀ M)} {x : ι} :
    x ∈ l.foldr ((·⊔·) ∘ Finsupp.support) ∅ ↔ ∃ (f : ι →₀ M)(hf : f ∈ l), x ∈ f.Support := by
  simp only [← Finset.sup_eq_union, ← List.foldr_map, ← Finsupp.mem_support_iff, ← exists_prop]
  induction' l with hd tl IH
  · simp
    
  · simp only [← IH, ← List.foldr_cons, ← Finset.mem_union, ← Finsupp.mem_support_iff, ← List.mem_cons_iffₓ]
    constructor
    · rintro (h | h)
      · exact ⟨hd, Or.inl rfl, h⟩
        
      · exact h.imp fun f hf => hf.imp_left Or.inr
        
      
    · rintro ⟨f, rfl | hf, h⟩
      · exact Or.inl h
        
      · exact Or.inr ⟨f, hf, h⟩
        
      
    

theorem Multiset.mem_sup_map_support_iff [Zero M] {s : Multiset (ι →₀ M)} {x : ι} :
    x ∈ (s.map Finsupp.support).sup ↔ ∃ (f : ι →₀ M)(hf : f ∈ s), x ∈ f.Support :=
  (Quot.induction_on s) fun _ => by
    simpa using List.mem_foldr_sup_support_iff

theorem Finset.mem_sup_support_iff [Zero M] {s : Finset (ι →₀ M)} {x : ι} :
    x ∈ s.sup Finsupp.support ↔ ∃ (f : ι →₀ M)(hf : f ∈ s), x ∈ f.Support :=
  Multiset.mem_sup_map_support_iff

theorem List.support_sum_eq [AddMonoidₓ M] (l : List (ι →₀ M)) (hl : l.Pairwise (Disjoint on Finsupp.support)) :
    l.Sum.Support = l.foldr ((·⊔·) ∘ Finsupp.support) ∅ := by
  induction' l with hd tl IH
  · simp
    
  · simp only [← List.pairwise_cons] at hl
    simp only [← List.sum_cons, ← List.foldr_cons, ← Function.comp_app]
    rw [Finsupp.support_add_eq, IH hl.right, Finset.sup_eq_union]
    suffices Disjoint hd.support (tl.foldr ((·⊔·) ∘ Finsupp.support) ∅) by
      exact Finset.disjoint_of_subset_right (List.support_sum_subset _) this
    · rw [← List.foldr_map, ← Finset.bot_eq_empty, List.foldr_sup_eq_sup_to_finset]
      rw [Finset.disjoint_sup_right]
      intro f hf
      simp only [← List.mem_to_finset, ← List.mem_mapₓ] at hf
      obtain ⟨f, hf, rfl⟩ := hf
      exact hl.left _ hf
      
    

theorem Multiset.support_sum_eq [AddCommMonoidₓ M] (s : Multiset (ι →₀ M))
    (hs : s.Pairwise (Disjoint on Finsupp.support)) : s.Sum.Support = (s.map Finsupp.support).sup := by
  induction s using Quot.induction_on
  obtain ⟨l, hl, hd⟩ := hs
  convert List.support_sum_eq _ _
  · simp
    
  · simp
    
  · simp only [← Multiset.quot_mk_to_coe'', ← Multiset.coe_map, ← Multiset.coe_eq_coe] at hl
    exact hl.symm.pairwise hd fun _ _ h => Disjoint.symm h
    

theorem Finset.support_sum_eq [AddCommMonoidₓ M] (s : Finset (ι →₀ M))
    (hs : (s : Set (ι →₀ M)).PairwiseDisjoint Finsupp.support) : (s.Sum id).Support = Finset.sup s Finsupp.support := by
  classical
  convert Multiset.support_sum_eq s.1 _
  · exact (Finset.sum_val _).symm
    
  · obtain ⟨l, hl, hn⟩ : ∃ l : List (ι →₀ M), l.toFinset = s ∧ l.Nodup := by
      refine' ⟨s.to_list, _, Finset.nodup_to_list _⟩
      simp
    subst hl
    rwa [List.to_finset_val, list.dedup_eq_self.mpr hn, Multiset.pairwise_coe_iff_pairwise, ←
      List.pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint hn]
    intro x y hxy
    exact symmetric_disjoint hxy
    

