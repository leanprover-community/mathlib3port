import Mathbin.Analysis.Convex.Combination 
import Mathbin.LinearAlgebra.AffineSpace.Independent 
import Mathbin.Tactic.FieldSimp

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convex_hull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/


open Set Finset

open_locale BigOperators

universe u

variable{𝕜 : Type _}{E : Type u}[LinearOrderedField 𝕜][AddCommGroupₓ E][Module 𝕜 E]

namespace Caratheodory

-- error in Analysis.Convex.Caratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `x` is in the convex hull of some finset `t` whose elements are not affine-independent,
then it is in the convex hull of a strict subset of `t`. -/
theorem mem_convex_hull_erase
[decidable_eq E]
{t : finset E}
(h : «expr¬ »(affine_independent 𝕜 (coe : t → E)))
{x : E}
(m : «expr ∈ »(x, convex_hull 𝕜 («expr↑ »(t) : set E))) : «expr∃ , »((y : («expr↑ »(t) : set E)), «expr ∈ »(x, convex_hull 𝕜 («expr↑ »(t.erase y) : set E))) :=
begin
  simp [] [] ["only"] ["[", expr finset.convex_hull_eq, ",", expr mem_set_of_eq, "]"] [] ["at", ident m, "⊢"],
  obtain ["⟨", ident f, ",", ident fpos, ",", ident fsum, ",", ident rfl, "⟩", ":=", expr m],
  obtain ["⟨", ident g, ",", ident gcombo, ",", ident gsum, ",", ident gpos, "⟩", ":=", expr exists_nontrivial_relation_sum_zero_of_not_affine_ind h],
  replace [ident gpos] [] [":=", expr exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos],
  clear [ident h],
  let [ident s] [] [":=", expr t.filter (λ z : E, «expr < »(0, g z))],
  obtain ["⟨", ident i₀, ",", ident mem, ",", ident w, "⟩", ":", expr «expr∃ , »((i₀ «expr ∈ » s), ∀
    i «expr ∈ » s, «expr ≤ »(«expr / »(f i₀, g i₀), «expr / »(f i, g i)))],
  { apply [expr s.exists_min_image (λ z, «expr / »(f z, g z))],
    obtain ["⟨", ident x, ",", ident hx, ",", ident hgx, "⟩", ":", expr «expr∃ , »((x «expr ∈ » t), «expr < »(0, g x)), ":=", expr gpos],
    exact [expr ⟨x, mem_filter.mpr ⟨hx, hgx⟩⟩] },
  have [ident hg] [":", expr «expr < »(0, g i₀)] [":=", expr by { rw [expr mem_filter] ["at", ident mem],
     exact [expr mem.2] }],
  have [ident hi₀] [":", expr «expr ∈ »(i₀, t)] [":=", expr filter_subset _ _ mem],
  let [ident k] [":", expr E → 𝕜] [":=", expr λ z, «expr - »(f z, «expr * »(«expr / »(f i₀, g i₀), g z))],
  have [ident hk] [":", expr «expr = »(k i₀, 0)] [":=", expr by field_simp [] ["[", expr k, ",", expr ne_of_gt hg, "]"] [] []],
  have [ident ksum] [":", expr «expr = »(«expr∑ in , »((e), t.erase i₀, k e), 1)] [],
  { calc
      «expr = »(«expr∑ in , »((e), t.erase i₀, k e), «expr∑ in , »((e), t, k e)) : by conv_rhs [] [] { rw ["[", "<-", expr insert_erase hi₀, ",", expr sum_insert (not_mem_erase i₀ t), ",", expr hk, ",", expr zero_add, "]"] }
      «expr = »(..., «expr∑ in , »((e), t, «expr - »(f e, «expr * »(«expr / »(f i₀, g i₀), g e)))) : rfl
      «expr = »(..., 1) : by rw ["[", expr sum_sub_distrib, ",", expr fsum, ",", "<-", expr mul_sum, ",", expr gsum, ",", expr mul_zero, ",", expr sub_zero, "]"] [] },
  refine [expr ⟨⟨i₀, hi₀⟩, k, _, ksum, _⟩],
  { simp [] [] ["only"] ["[", expr and_imp, ",", expr sub_nonneg, ",", expr mem_erase, ",", expr ne.def, ",", expr subtype.coe_mk, "]"] [] [],
    intros [ident e, ident hei₀, ident het],
    by_cases [expr hes, ":", expr «expr ∈ »(e, s)],
    { have [ident hge] [":", expr «expr < »(0, g e)] [":=", expr by { rw [expr mem_filter] ["at", ident hes],
         exact [expr hes.2] }],
      rw ["<-", expr le_div_iff hge] [],
      exact [expr w _ hes] },
    { calc
        «expr ≤ »(_, 0) : mul_nonpos_of_nonneg_of_nonpos _ _
        «expr ≤ »(..., f e) : fpos e het,
      { apply [expr div_nonneg (fpos i₀ (mem_of_subset (filter_subset _ t) mem)) (le_of_lt hg)] },
      { simpa [] [] ["only"] ["[", expr mem_filter, ",", expr het, ",", expr true_and, ",", expr not_lt, "]"] [] ["using", expr hes] } } },
  { simp [] [] ["only"] ["[", expr subtype.coe_mk, ",", expr center_mass_eq_of_sum_1 _ id ksum, ",", expr id, "]"] [] [],
    calc
      «expr = »(«expr∑ in , »((e), t.erase i₀, «expr • »(k e, e)), «expr∑ in , »((e), t, «expr • »(k e, e))) : sum_erase _ (by rw ["[", expr hk, ",", expr zero_smul, "]"] [])
      «expr = »(..., «expr∑ in , »((e), t, «expr • »(«expr - »(f e, «expr * »(«expr / »(f i₀, g i₀), g e)), e))) : rfl
      «expr = »(..., t.center_mass f id) : _,
    simp [] [] ["only"] ["[", expr sub_smul, ",", expr mul_smul, ",", expr sum_sub_distrib, ",", "<-", expr smul_sum, ",", expr gcombo, ",", expr smul_zero, ",", expr sub_zero, ",", expr center_mass, ",", expr fsum, ",", expr inv_one, ",", expr one_smul, ",", expr id.def, "]"] [] [] }
end

variable{s : Set E}{x : E}(hx : x ∈ convexHull 𝕜 s)

include hx

/-- Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
cardinality, whose convex hull contains `x`. -/
noncomputable def min_card_finset_of_mem_convex_hull : Finset E :=
  Function.argminOn Finset.card Nat.lt_wf { t | «expr↑ » t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) }
    (by 
      simpa only [convex_hull_eq_union_convex_hull_finite_subsets s, exists_prop, mem_Union] using hx)

theorem min_card_finset_of_mem_convex_hull_subseteq : «expr↑ » (min_card_finset_of_mem_convex_hull hx) ⊆ s :=
  (Function.argmin_on_mem _ _ { t:Finset E | «expr↑ » t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1

theorem mem_min_card_finset_of_mem_convex_hull : x ∈ convexHull 𝕜 (min_card_finset_of_mem_convex_hull hx : Set E) :=
  (Function.argmin_on_mem _ _ { t:Finset E | «expr↑ » t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2

theorem min_card_finset_of_mem_convex_hull_nonempty : (min_card_finset_of_mem_convex_hull hx).Nonempty :=
  by 
    rw [←Finset.coe_nonempty, ←@convex_hull_nonempty_iff 𝕜]
    exact ⟨x, mem_min_card_finset_of_mem_convex_hull hx⟩

theorem min_card_finset_of_mem_convex_hull_card_le_card {t : Finset E} (ht₁ : «expr↑ » t ⊆ s)
  (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : (min_card_finset_of_mem_convex_hull hx).card ≤ t.card :=
  Function.argmin_on_le _ _ _ ⟨ht₁, ht₂⟩

-- error in Analysis.Convex.Caratheodory: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem affine_independent_min_card_finset_of_mem_convex_hull : affine_independent 𝕜 (coe : min_card_finset_of_mem_convex_hull hx → E) :=
begin
  let [ident k] [] [":=", expr «expr - »((min_card_finset_of_mem_convex_hull hx).card, 1)],
  have [ident hk] [":", expr «expr = »((min_card_finset_of_mem_convex_hull hx).card, «expr + »(k, 1))] [],
  { exact [expr (nat.succ_pred_eq_of_pos (finset.card_pos.mpr (min_card_finset_of_mem_convex_hull_nonempty hx))).symm] },
  classical,
  by_contra [],
  obtain ["⟨", ident p, ",", ident hp, "⟩", ":=", expr mem_convex_hull_erase h (mem_min_card_finset_of_mem_convex_hull hx)],
  have [ident contra] [] [":=", expr min_card_finset_of_mem_convex_hull_card_le_card hx (set.subset.trans (finset.erase_subset «expr↑ »(p) (min_card_finset_of_mem_convex_hull hx)) (min_card_finset_of_mem_convex_hull_subseteq hx)) hp],
  rw ["[", "<-", expr not_lt, "]"] ["at", ident contra],
  apply [expr contra],
  erw ["[", expr card_erase_of_mem p.2, ",", expr hk, "]"] [],
  exact [expr lt_add_one _]
end

end Caratheodory

variable{s : Set E}

/-- **Carathéodory's convexity theorem** -/
theorem convex_hull_eq_union :
  convexHull 𝕜 s =
    ⋃(t : Finset E)(hss : «expr↑ » t ⊆ s)(hai : AffineIndependent 𝕜 (coeₓ : t → E)), convexHull 𝕜 («expr↑ » t) :=
  by 
    apply Set.Subset.antisymm
    ·
      intro x hx 
      simp only [exists_prop, Set.mem_Union]
      exact
        ⟨Caratheodory.minCardFinsetOfMemConvexHull hx, Caratheodory.min_card_finset_of_mem_convex_hull_subseteq hx,
          Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull hx,
          Caratheodory.mem_min_card_finset_of_mem_convex_hull hx⟩
    ·
      iterate 3
        convert Set.Union_subset _ 
        intro 
      exact convex_hull_mono ‹_›

/-- A more explicit version of `convex_hull_eq_union`. -/
theorem eq_pos_convex_span_of_mem_convex_hull {x : E} (hx : x ∈ convexHull 𝕜 s) :
  ∃ (ι : Sort (u + 1))(_ : Fintype ι),
    by 
      exact
        ∃ (z : ι → E)(w : ι → 𝕜)(hss : Set.Range z ⊆ s)(hai : AffineIndependent 𝕜 z)(hw : ∀ i, 0 < w i),
          (∑i, w i) = 1 ∧ (∑i, w i • z i) = x :=
  by 
    rw [convex_hull_eq_union] at hx 
    simp only [exists_prop, Set.mem_Union] at hx 
    obtain ⟨t, ht₁, ht₂, ht₃⟩ := hx 
    simp only [t.convex_hull_eq, exists_prop, Set.mem_set_of_eq] at ht₃ 
    obtain ⟨w, hw₁, hw₂, hw₃⟩ := ht₃ 
    let t' := t.filter fun i => w i ≠ 0
    refine' ⟨t', t'.fintype_coe_sort, (coeₓ : t' → E), w ∘ (coeₓ : t' → E), _, _, _, _, _⟩
    ·
      rw [Subtype.range_coe_subtype]
      exact subset.trans (Finset.filter_subset _ t) ht₁
    ·
      exact ht₂.comp_embedding ⟨_, inclusion_injective (Finset.filter_subset (fun i => w i ≠ 0) t)⟩
    ·
      exact fun i => (hw₁ _ (finset.mem_filter.mp i.2).1).lt_of_ne (finset.mem_filter.mp i.property).2.symm
    ·
      erw [Finset.sum_attach, Finset.sum_filter_ne_zero, hw₂]
    ·
      change (∑i : t' in t'.attach, (fun e => w e • e) («expr↑ » i)) = x 
      erw [Finset.sum_attach, Finset.sum_filter_of_ne]
      ·
        rw [t.center_mass_eq_of_sum_1 id hw₂] at hw₃ 
        exact hw₃
      ·
        intro e he hwe contra 
        apply hwe 
        rw [contra, zero_smul]

