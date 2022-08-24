/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathbin.Combinatorics.SimpleGraph.Basic
import Mathbin.Order.Partition.Finpartition

/-!
# Edge density

This file defines the number and density of edges of a relation/graph.

## Main declarations

Between two finsets of vertices,
* `rel.interedges`: Finset of edges of a relation.
* `rel.edge_density`: Edge density of a relation.
* `simple_graph.interedges`: Finset of edges of a graph.
* `simple_graph.edge_density`: Edge density of a graph.
-/


open Finset

open BigOperators

variable {ι κ α β : Type _}

/-! ### Density of a relation -/


namespace Rel

section Asymmetric

variable (r : α → β → Prop) [∀ a, DecidablePred (r a)] {s s₁ s₂ : Finset α} {t t₁ t₂ : Finset β} {a : α} {b : β} {δ : ℚ}

/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s : Finset α) (t : Finset β) : Finset (α × β) :=
  (s ×ˢ t).filter fun e => r e.1 e.2

/-- Edge density of a relation between two finsets of vertices. -/
def edgeDensity (s : Finset α) (t : Finset β) : ℚ :=
  (interedges r s t).card / (s.card * t.card)

variable {r}

theorem mem_interedges_iff {x : α × β} : x ∈ interedges r s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ r x.1 x.2 := by
  simp only [interedges, and_assoc, mem_filter, Finset.mem_product]

theorem mk_mem_interedges_iff : (a, b) ∈ interedges r s t ↔ a ∈ s ∧ b ∈ t ∧ r a b :=
  mem_interedges_iff

@[simp]
theorem interedges_empty_left (t : Finset β) : interedges r ∅ t = ∅ := by
  rw [interedges, Finset.empty_product, filter_empty]

theorem interedges_mono (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) : interedges r s₂ t₂ ⊆ interedges r s₁ t₁ := fun x => by
  simp_rw [mem_interedges_iff]
  exact fun h => ⟨hs h.1, ht h.2.1, h.2.2⟩

variable (r)

theorem card_interedges_add_card_interedges_compl (s : Finset α) (t : Finset β) :
    (interedges r s t).card + (interedges (fun x y => ¬r x y) s t).card = s.card * t.card := by
  classical
  rw [← card_product, interedges, interedges, ← card_union_eq, filter_union_filter_neg_eq]
  convert disjoint_filter.2 fun x _ => not_not.2

section DecidableEq

variable [DecidableEq α] [DecidableEq β]

theorem interedges_disjoint_left {s s' : Finset α} (hs : Disjoint s s') (t : Finset β) :
    Disjoint (interedges r s t) (interedges r s' t) := by
  rintro x hx
  rw [inf_eq_inter, mem_inter, mem_interedges_iff, mem_interedges_iff] at hx
  exact hs (mem_inter.2 ⟨hx.1.1, hx.2.1⟩)

theorem interedges_disjoint_right (s : Finset α) {t t' : Finset β} (ht : Disjoint t t') :
    Disjoint (interedges r s t) (interedges r s t') := by
  rintro x hx
  rw [inf_eq_inter, mem_inter, mem_interedges_iff, mem_interedges_iff] at hx
  exact ht (mem_inter.2 ⟨hx.1.2.1, hx.2.2.1⟩)

theorem interedges_bUnion_left (s : Finset ι) (t : Finset β) (f : ι → Finset α) :
    interedges r (s.bUnion f) t = s.bUnion fun a => interedges r (f a) t :=
  ext fun a => by
    simp only [mem_bUnion, mem_interedges_iff, exists_and_distrib_right]

theorem interedges_bUnion_right (s : Finset α) (t : Finset ι) (f : ι → Finset β) :
    interedges r s (t.bUnion f) = t.bUnion fun b => interedges r s (f b) :=
  ext fun a => by
    simp only [mem_interedges_iff, mem_bUnion, ← exists_and_distrib_left, ← exists_and_distrib_right]

theorem interedges_bUnion (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset β) :
    interedges r (s.bUnion f) (t.bUnion g) = (s ×ˢ t).bUnion fun ab => interedges r (f ab.1) (g ab.2) := by
  simp_rw [product_bUnion, interedges_bUnion_left, interedges_bUnion_right]

end DecidableEq

theorem card_interedges_le_mul (s : Finset α) (t : Finset β) : (interedges r s t).card ≤ s.card * t.card :=
  (card_filter_le _ _).trans (card_product _ _).le

theorem edge_density_nonneg (s : Finset α) (t : Finset β) : 0 ≤ edgeDensity r s t := by
  apply div_nonneg <;> exact_mod_cast Nat.zero_leₓ _

theorem edge_density_le_one (s : Finset α) (t : Finset β) : edgeDensity r s t ≤ 1 :=
  div_le_one_of_le
      (by
        exact_mod_cast card_interedges_le_mul _ _ _) <|
    by
    exact_mod_cast Nat.zero_leₓ _

theorem edge_density_add_edge_density_compl (hs : s.Nonempty) (ht : t.Nonempty) :
    edgeDensity r s t + edgeDensity (fun x y => ¬r x y) s t = 1 := by
  rw [edge_density, edge_density, div_add_div_same, div_eq_one_iff_eq]
  · exact_mod_cast card_interedges_add_card_interedges_compl r s t
    
  · exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne'
    

@[simp]
theorem edge_density_empty_left (t : Finset β) : edgeDensity r ∅ t = 0 := by
  rw [edge_density, Finset.card_empty, Nat.cast_zeroₓ, zero_mul, div_zero]

@[simp]
theorem edge_density_empty_right (s : Finset α) : edgeDensity r s ∅ = 0 := by
  rw [edge_density, Finset.card_empty, Nat.cast_zeroₓ, mul_zero, div_zero]

theorem card_interedges_finpartition_left [DecidableEq α] (P : Finpartition s) (t : Finset β) :
    (interedges r s t).card = ∑ a in P.parts, (interedges r a t).card := by
  classical
  simp_rw [← P.bUnion_parts, interedges_bUnion_left, id.def]
  rw [card_bUnion]
  exact fun x hx y hy h => interedges_disjoint_left r (P.disjoint hx hy h) _

theorem card_interedges_finpartition_right [DecidableEq β] (s : Finset α) (P : Finpartition t) :
    (interedges r s t).card = ∑ b in P.parts, (interedges r s b).card := by
  classical
  simp_rw [← P.bUnion_parts, interedges_bUnion_right, id]
  rw [card_bUnion]
  exact fun x hx y hy h => interedges_disjoint_right r _ (P.disjoint hx hy h)

theorem card_interedges_finpartition [DecidableEq α] [DecidableEq β] (P : Finpartition s) (Q : Finpartition t) :
    (interedges r s t).card = ∑ ab in P.parts ×ˢ Q.parts, (interedges r ab.1 ab.2).card := by
  simp_rw [card_interedges_finpartition_left _ P, card_interedges_finpartition_right _ _ Q, sum_product]

theorem mul_edge_density_le_edge_density (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty) (ht₂ : t₂.Nonempty) :
    (s₂.card : ℚ) / s₁.card * (t₂.card / t₁.card) * edgeDensity r s₂ t₂ ≤ edgeDensity r s₁ t₁ := by
  have hst : (s₂.card : ℚ) * t₂.card ≠ 0 := by
    simp [hs₂.ne_empty, ht₂.ne_empty]
  rw [edge_density, edge_density, div_mul_div_comm, mul_comm, div_mul_div_cancel _ hst]
  refine'
    div_le_div_of_le
      (by
        exact_mod_cast (s₁.card * t₁.card).zero_le)
      _
  exact_mod_cast card_le_of_subset (interedges_mono hs ht)

theorem edge_density_sub_edge_density_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) : edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁ ≤ 1 - s₂.card / s₁.card * (t₂.card / t₁.card) := by
  refine' (sub_le_sub_left (mul_edge_density_le_edge_density r hs ht hs₂ ht₂) _).trans _
  refine' le_transₓ _ (mul_le_of_le_one_right _ (edge_density_le_one r s₂ t₂))
  · rw [sub_mul, one_mulₓ]
    
  refine' sub_nonneg_of_le (mul_le_one _ (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _) <;>
    exact div_le_one_of_le (Nat.cast_le.2 (card_le_of_subset ‹_›)) (Nat.cast_nonneg _)

theorem abs_edge_density_sub_edge_density_le_one_sub_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hs₂ : s₂.Nonempty)
    (ht₂ : t₂.Nonempty) :
    abs (edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁) ≤ 1 - s₂.card / s₁.card * (t₂.card / t₁.card) := by
  have habs : abs (edge_density r s₂ t₂ - edge_density r s₁ t₁) ≤ 1 := by
    rw [abs_sub_le_iff, ← sub_zero (1 : ℚ)]
    constructor <;> exact sub_le_sub (edge_density_le_one r _ _) (edge_density_nonneg r _ _)
  refine' abs_sub_le_iff.2 ⟨edge_density_sub_edge_density_le_one_sub_mul r hs ht hs₂ ht₂, _⟩
  rw [← add_sub_cancel (edge_density r s₁ t₁) (edge_density (fun x y => ¬r x y) s₁ t₁), ←
    add_sub_cancel (edge_density r s₂ t₂) (edge_density (fun x y => ¬r x y) s₂ t₂),
    edge_density_add_edge_density_compl _ (hs₂.mono hs) (ht₂.mono ht), edge_density_add_edge_density_compl _ hs₂ ht₂,
    sub_sub_sub_cancel_left]
  exact edge_density_sub_edge_density_le_one_sub_mul _ hs ht hs₂ ht₂

theorem abs_edge_density_sub_edge_density_le_two_mul_sub_sq (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hδ₀ : 0 ≤ δ) (hδ₁ : δ < 1)
    (hs₂ : (1 - δ) * s₁.card ≤ s₂.card) (ht₂ : (1 - δ) * t₁.card ≤ t₂.card) :
    abs (edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁) ≤ 2 * δ - δ ^ 2 := by
  have hδ' : 0 ≤ 2 * δ - δ ^ 2 := by
    rw [sub_nonneg, sq]
    exact
      mul_le_mul_of_nonneg_right
        (hδ₁.le.trans
          (by
            norm_num))
        hδ₀
  rw [← sub_pos] at hδ₁
  simp only [edge_density]
  obtain rfl | hs₂' := s₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zeroₓ] at hs₂
    simpa [(nonpos_of_mul_nonpos_right hs₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
    
  obtain rfl | ht₂' := t₂.eq_empty_or_nonempty
  · rw [Finset.card_empty, Nat.cast_zeroₓ] at ht₂
    simpa [(nonpos_of_mul_nonpos_right ht₂ hδ₁).antisymm (Nat.cast_nonneg _)] using hδ'
    
  rw
    [show 2 * δ - δ ^ 2 = 1 - (1 - δ) * (1 - δ) by
      ring]
  refine' (abs_edge_density_sub_edge_density_le_one_sub_mul r hs ht hs₂' ht₂').trans _
  apply sub_le_sub_left (mul_le_mul ((le_div_iff _).2 hs₂) ((le_div_iff _).2 ht₂) hδ₁.le _)
  · exact_mod_cast (hs₂'.mono hs).card_pos
    
  · exact_mod_cast (ht₂'.mono ht).card_pos
    
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    

/-- If `s₂ ⊆ s₁`, `t₂ ⊆ t₁` and they take up all but a `δ`-proportion, then the difference in edge
densities is at most `2 * δ`. -/
theorem abs_edge_density_sub_edge_density_le_two_mul (hs : s₂ ⊆ s₁) (ht : t₂ ⊆ t₁) (hδ : 0 ≤ δ)
    (hscard : (1 - δ) * s₁.card ≤ s₂.card) (htcard : (1 - δ) * t₁.card ≤ t₂.card) :
    abs (edgeDensity r s₂ t₂ - edgeDensity r s₁ t₁) ≤ 2 * δ := by
  cases lt_or_leₓ δ 1
  · exact
      (abs_edge_density_sub_edge_density_le_two_mul_sub_sq r hs ht hδ h hscard htcard).trans
        ((sub_le_self_iff _).2 <| sq_nonneg δ)
    
  rw [two_mul]
  refine' (abs_sub _ _).trans (add_le_add (le_transₓ _ h) (le_transₓ _ h)) <;>
    · rw [abs_of_nonneg]
      exact_mod_cast edge_density_le_one r _ _
      exact_mod_cast edge_density_nonneg r _ _
      

end Asymmetric

section Symmetric

variable (r : α → α → Prop) [DecidableRel r] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

variable {r} (hr : Symmetric r)

include hr

@[simp]
theorem swap_mem_interedges_iff {x : α × α} : x.swap ∈ interedges r s t ↔ x ∈ interedges r t s := by
  rw [mem_interedges_iff, mem_interedges_iff, hr.iff]
  exact And.left_comm

theorem mk_mem_interedges_comm : (a, b) ∈ interedges r s t ↔ (b, a) ∈ interedges r t s :=
  @swap_mem_interedges_iff _ _ _ _ _ hr (b, a)

theorem card_interedges_comm (s t : Finset α) : (interedges r s t).card = (interedges r t s).card :=
  Finset.card_congr (fun (x : α × α) _ => x.swap) (fun x => (swap_mem_interedges_iff hr).2)
    (fun _ _ _ _ h => Prod.swap_injective h) fun x h => ⟨x.swap, (swap_mem_interedges_iff hr).2 h, x.swap_swap⟩

theorem edge_density_comm (s t : Finset α) : edgeDensity r s t = edgeDensity r t s := by
  rw [edge_density, mul_comm, card_interedges_comm hr, edge_density]

end Symmetric

end Rel

open Rel

/-! ### Density of a graph -/


namespace SimpleGraph

variable (G : SimpleGraph α) [DecidableRel G.Adj] {s s₁ s₂ t t₁ t₂ : Finset α} {a b : α}

/-- Finset of edges of a relation between two finsets of vertices. -/
def interedges (s t : Finset α) : Finset (α × α) :=
  interedges G.Adj s t

/-- Density of edges of a graph between two finsets of vertices. -/
def edgeDensity : Finset α → Finset α → ℚ :=
  edgeDensity G.Adj

theorem interedges_def (s t : Finset α) : G.interedges s t = (s ×ˢ t).filter fun e => G.Adj e.1 e.2 :=
  rfl

theorem edge_density_def (s t : Finset α) : G.edgeDensity s t = (G.interedges s t).card / (s.card * t.card) :=
  rfl

@[simp]
theorem card_interedges_div_card (s t : Finset α) :
    ((G.interedges s t).card : ℚ) / (s.card * t.card) = G.edgeDensity s t :=
  rfl

theorem mem_interedges_iff {x : α × α} : x ∈ G.interedges s t ↔ x.1 ∈ s ∧ x.2 ∈ t ∧ G.Adj x.1 x.2 :=
  mem_interedges_iff

theorem mk_mem_interedges_iff : (a, b) ∈ G.interedges s t ↔ a ∈ s ∧ b ∈ t ∧ G.Adj a b :=
  mk_mem_interedges_iff

@[simp]
theorem interedges_empty_left (t : Finset α) : G.interedges ∅ t = ∅ :=
  interedges_empty_left _

theorem interedges_mono : s₂ ⊆ s₁ → t₂ ⊆ t₁ → G.interedges s₂ t₂ ⊆ G.interedges s₁ t₁ :=
  interedges_mono

section DecidableEq

variable [DecidableEq α]

theorem interedges_disjoint_left (hs : Disjoint s₁ s₂) (t : Finset α) :
    Disjoint (G.interedges s₁ t) (G.interedges s₂ t) :=
  interedges_disjoint_left _ hs _

theorem interedges_disjoint_right (s : Finset α) (ht : Disjoint t₁ t₂) :
    Disjoint (G.interedges s t₁) (G.interedges s t₂) :=
  interedges_disjoint_right _ _ ht

theorem interedges_bUnion_left (s : Finset ι) (t : Finset α) (f : ι → Finset α) :
    G.interedges (s.bUnion f) t = s.bUnion fun a => G.interedges (f a) t :=
  interedges_bUnion_left _ _ _ _

theorem interedges_bUnion_right (s : Finset α) (t : Finset ι) (f : ι → Finset α) :
    G.interedges s (t.bUnion f) = t.bUnion fun b => G.interedges s (f b) :=
  interedges_bUnion_right _ _ _ _

theorem interedges_bUnion (s : Finset ι) (t : Finset κ) (f : ι → Finset α) (g : κ → Finset α) :
    G.interedges (s.bUnion f) (t.bUnion g) = (s ×ˢ t).bUnion fun ab => G.interedges (f ab.1) (g ab.2) :=
  interedges_bUnion _ _ _ _ _

theorem card_interedges_add_card_interedges_compl (h : Disjoint s t) :
    (G.interedges s t).card + (Gᶜ.interedges s t).card = s.card * t.card := by
  rw [← card_product, interedges_def, interedges_def]
  have : ((s ×ˢ t).filter fun e => Gᶜ.Adj e.1 e.2) = (s ×ˢ t).filter fun e => ¬G.adj e.1 e.2 := by
    refine' filter_congr fun x hx => _
    rw [mem_product] at hx
    rw [compl_adj, and_iff_right (h.forall_ne_finset hx.1 hx.2)]
  rw [this, ← card_union_eq, filter_union_filter_neg_eq]
  exact disjoint_filter.2 fun x _ => not_not.2

theorem edge_density_add_edge_density_compl (hs : s.Nonempty) (ht : t.Nonempty) (h : Disjoint s t) :
    G.edgeDensity s t + Gᶜ.edgeDensity s t = 1 := by
  rw [edge_density_def, edge_density_def, div_add_div_same, div_eq_one_iff_eq]
  · exact_mod_cast card_interedges_add_card_interedges_compl _ h
    
  · exact_mod_cast (mul_pos hs.card_pos ht.card_pos).ne'
    

end DecidableEq

theorem card_interedges_le_mul (s t : Finset α) : (G.interedges s t).card ≤ s.card * t.card :=
  card_interedges_le_mul _ _ _

theorem edge_density_nonneg (s t : Finset α) : 0 ≤ G.edgeDensity s t :=
  edge_density_nonneg _ _ _

theorem edge_density_le_one (s t : Finset α) : G.edgeDensity s t ≤ 1 :=
  edge_density_le_one _ _ _

@[simp]
theorem edge_density_empty_left (t : Finset α) : G.edgeDensity ∅ t = 0 :=
  edge_density_empty_left _ _

@[simp]
theorem edge_density_empty_right (s : Finset α) : G.edgeDensity s ∅ = 0 :=
  edge_density_empty_right _ _

@[simp]
theorem swap_mem_interedges_iff {x : α × α} : x.swap ∈ G.interedges s t ↔ x ∈ G.interedges t s :=
  swap_mem_interedges_iff G.symm

theorem mk_mem_interedges_comm : (a, b) ∈ G.interedges s t ↔ (b, a) ∈ G.interedges t s :=
  mk_mem_interedges_comm G.symm

theorem edge_density_comm (s t : Finset α) : G.edgeDensity s t = G.edgeDensity t s :=
  edge_density_comm G.symm s t

end SimpleGraph

