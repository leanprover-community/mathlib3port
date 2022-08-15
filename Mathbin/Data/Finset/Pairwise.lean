/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Data.Finset.Lattice

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `set.pairwise_disjoint` and `finset`,
as well as the interaction of `list.pairwise disjoint` and the condition of
`disjoint` on `list.to_finset`, in `set` form.
-/


open Finset

variable {α ι ι' : Type _}

instance [DecidableEq α] {r : α → α → Prop} [DecidableRel r] {s : Finset α} : Decidable ((s : Set α).Pairwise r) :=
  decidableOfIff' (∀, ∀ a ∈ s, ∀, ∀, ∀ b ∈ s, ∀, a ≠ b → r a b) Iff.rfl

theorem Finset.pairwise_disjoint_range_singleton [DecidableEq α] :
    (Set.Range (singleton : α → Finset α)).PairwiseDisjoint id := by
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h
  exact disjoint_singleton.2 (ne_of_apply_ne _ h)

namespace Set

theorem PairwiseDisjoint.elim_finset [DecidableEq α] {s : Set ι} {f : ι → Finset α} (hs : s.PairwiseDisjoint f)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

theorem PairwiseDisjoint.image_finset_of_le [DecidableEq ι] [SemilatticeInf α] [OrderBot α] {s : Finset ι} {f : ι → α}
    (hs : (s : Set ι).PairwiseDisjoint f) {g : ι → ι} (hf : ∀ a, f (g a) ≤ f a) :
    (s.Image g : Set ι).PairwiseDisjoint f := by
  rw [coe_image]
  exact hs.image_of_le hf

variable [Lattice α] [OrderBot α]

/-- Bind operation for `set.pairwise_disjoint`. In a complete lattice, you can use
`set.pairwise_disjoint.bUnion`. -/
theorem PairwiseDisjoint.bUnion_finset {s : Set ι'} {g : ι' → Finset ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => (g i').sup f) (hg : ∀, ∀ i ∈ s, ∀, (g i : Set ι).PairwiseDisjoint f) :
    (⋃ i ∈ s, ↑(g i)).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_Union] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact
      hg d hd
        (by
          rwa [hcd] at ha)
        hb hab
    
  · exact (hs hc hd (ne_of_apply_ne _ hcd)).mono (Finset.le_sup ha) (Finset.le_sup hb)
    

end Set

namespace List

variable {β : Type _} [DecidableEq α] {r : α → α → Prop} {l : List α}

theorem pairwise_of_coe_to_finset_pairwise (hl : (l.toFinset : Set α).Pairwise r) (hn : l.Nodup) : l.Pairwise r := by
  induction' l with hd tl IH
  · simp
    
  simp only [← Set.pairwise_insert, ← pairwise_cons, ← to_finset_cons, ← Finset.coe_insert, ← Finset.mem_coe, ←
    mem_to_finset, ← Ne.def, ← nodup_cons] at hl hn⊢
  refine' ⟨fun x hx => (hl.right x hx _).left, IH hl.left hn.right⟩
  rintro rfl
  exact hn.left hx

theorem pairwise_iff_coe_to_finset_pairwise (hn : l.Nodup) (hs : Symmetric r) :
    (l.toFinset : Set α).Pairwise r ↔ l.Pairwise r := by
  refine' ⟨fun h => pairwise_of_coe_to_finset_pairwise h hn, fun h => _⟩
  induction' l with hd tl IH
  · simp
    
  simp only [← Set.pairwise_insert, ← to_finset_cons, ← Finset.coe_insert, ← Finset.mem_coe, ← mem_to_finset, ← Ne.def,
    ← pairwise_cons, ← nodup_cons] at hn h⊢
  exact ⟨IH hn.right h.right, fun x hx hne => ⟨h.left _ hx, hs (h.left _ hx)⟩⟩

theorem pairwise_disjoint_of_coe_to_finset_pairwise_disjoint {α ι} [SemilatticeInf α] [OrderBot α] [DecidableEq ι]
    {l : List ι} {f : ι → α} (hl : (l.toFinset : Set ι).PairwiseDisjoint f) (hn : l.Nodup) :
    l.Pairwise (_root_.disjoint on f) :=
  pairwise_of_coe_to_finset_pairwise hl hn

theorem pairwise_disjoint_iff_coe_to_finset_pairwise_disjoint {α ι} [SemilatticeInf α] [OrderBot α] [DecidableEq ι]
    {l : List ι} {f : ι → α} (hn : l.Nodup) :
    (l.toFinset : Set ι).PairwiseDisjoint f ↔ l.Pairwise (_root_.disjoint on f) :=
  pairwise_iff_coe_to_finset_pairwise hn (symmetric_disjoint.comap f)

end List

