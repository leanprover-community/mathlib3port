import Mathbin.Data.Finset.Lattice

/-!
# Relations holding pairwise on finite sets

In this file we prove a few results about the interaction of `set.pairwise_disjoint` and `finset`.
-/


open Finset

variable{α ι ι' : Type _}

theorem Finset.pairwise_disjoint_range_singleton [DecidableEq α] :
  (Set.Range (singleton : α → Finset α)).PairwiseDisjoint id :=
  by 
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ h 
    exact disjoint_singleton.2 (ne_of_apply_ne _ h)

namespace Set

theorem pairwise_disjoint.elim_finset [DecidableEq α] {s : Set ι} {f : ι → Finset α} (hs : s.pairwise_disjoint f)
  {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (a : α) (hai : a ∈ f i) (haj : a ∈ f j) : i = j :=
  hs.elim hi hj (Finset.not_disjoint_iff.2 ⟨a, hai, haj⟩)

theorem pairwise_disjoint.image_finset_of_le [DecidableEq ι] [SemilatticeInf α] [OrderBot α] {s : Finset ι} {f : ι → α}
  (hs : (s : Set ι).PairwiseDisjoint f) {g : ι → ι} (hf : ∀ a, f (g a) ≤ f a) :
  (s.image g : Set ι).PairwiseDisjoint f :=
  by 
    rw [coe_image]
    exact hs.image_of_le hf

variable[Lattice α][OrderBot α]

-- error in Data.Finset.Pairwise: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- Bind operation for `set.pairwise_disjoint`. In a complete lattice, you can use
`set.pairwise_disjoint.bUnion`. -/
theorem pairwise_disjoint.bUnion_finset
{s : set ι'}
{g : ι' → finset ι}
{f : ι → α}
(hs : s.pairwise_disjoint (λ i' : ι', (g i').sup f))
(hg : ∀
 i «expr ∈ » s, (g i : set ι).pairwise_disjoint f) : «expr⋃ , »((i «expr ∈ » s), «expr↑ »(g i)).pairwise_disjoint f :=
begin
  rintro [ident a, ident ha, ident b, ident hb, ident hab],
  simp_rw [expr set.mem_Union] ["at", ident ha, ident hb],
  obtain ["⟨", ident c, ",", ident hc, ",", ident ha, "⟩", ":=", expr ha],
  obtain ["⟨", ident d, ",", ident hd, ",", ident hb, "⟩", ":=", expr hb],
  obtain [ident hcd, "|", ident hcd, ":=", expr eq_or_ne (g c) (g d)],
  { exact [expr hg d hd a «expr ▸ »(hcd, ha) b hb hab] },
  { exact [expr (hs _ hc _ hd (ne_of_apply_ne _ hcd)).mono (finset.le_sup ha) (finset.le_sup hb)] }
end

end Set

