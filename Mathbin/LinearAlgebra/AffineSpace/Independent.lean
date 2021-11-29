import Mathbin.Data.Finset.Sort 
import Mathbin.Data.Fin.VecNotation 
import Mathbin.LinearAlgebra.AffineSpace.Combination 
import Mathbin.LinearAlgebra.AffineSpace.AffineEquiv 
import Mathbin.LinearAlgebra.Basis

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `affine_independent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.  A bundled type `simplex` is provided for finite
  affinely independent families of points, with an abbreviation
  `triangle` for the case of three points.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/


noncomputable theory

open_locale BigOperators Classical Affine

open Function

section AffineIndependent

variable (k : Type _) {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _}

include V

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ s : Finset ι w : ι → k, (∑i in s, w i) = 0 → s.weighted_vsub p w = (0 : V) → ∀ i _ : i ∈ s, w i = 0

/-- The definition of `affine_independent`. -/
theorem affine_independent_def (p : ι → P) :
  AffineIndependent k p ↔
    ∀ s : Finset ι w : ι → k, (∑i in s, w i) = 0 → s.weighted_vsub p w = (0 : V) → ∀ i _ : i ∈ s, w i = 0 :=
  Iff.rfl

/-- A family with at most one point is affinely independent. -/
theorem affine_independent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p :=
  fun s w h hs i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `finset.univ` (where
the sum of the weights is 0) are 0. -/
theorem affine_independent_iff_of_fintype [Fintype ι] (p : ι → P) :
  AffineIndependent k p ↔ ∀ w : ι → k, (∑i, w i) = 0 → Finset.univ.weightedVsub p w = (0 : V) → ∀ i, w i = 0 :=
  by 
    split 
    ·
      exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
    ·
      intro h s w hw hs i hi 
      rw [Finset.weighted_vsub_indicator_subset _ _ (Finset.subset_univ s)] at hs 
      rw [Set.sum_indicator_subset _ (Finset.subset_univ s)] at hw 
      replace h := h ((«expr↑ » s : Set ι).indicator w) hw hs i 
      simpa [hi] using h

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
theorem affine_independent_iff_linear_independent_vsub
(p : ι → P)
(i1 : ι) : «expr ↔ »(affine_independent k p, linear_independent k (λ
  i : {x // «expr ≠ »(x, i1)}, («expr -ᵥ »(p i, p i1) : V))) :=
begin
  split,
  { intro [ident h],
    rw [expr linear_independent_iff'] [],
    intros [ident s, ident g, ident hg, ident i, ident hi],
    set [] [ident f] [":", expr ι → k] [":="] [expr λ
     x, if hx : «expr = »(x, i1) then «expr- »(«expr∑ in , »((y), s, g y)) else g ⟨x, hx⟩] ["with", ident hfdef],
    let [ident s2] [":", expr finset ι] [":=", expr insert i1 (s.map (embedding.subtype _))],
    have [ident hfg] [":", expr ∀ x : {x // «expr ≠ »(x, i1)}, «expr = »(g x, f x)] [],
    { intro [ident x],
      rw [expr hfdef] [],
      dsimp ["only"] ["[", "]"] [] [],
      erw ["[", expr dif_neg x.property, ",", expr subtype.coe_eta, "]"] [] },
    rw [expr hfg] [],
    have [ident hf] [":", expr «expr = »(«expr∑ in , »((ι), s2, f ι), 0)] [],
    { rw ["[", expr finset.sum_insert (finset.not_mem_map_subtype_of_not_property s (not_not.2 rfl)), ",", expr finset.sum_subtype_map_embedding (λ
        x hx, (hfg x).symm), "]"] [],
      rw [expr hfdef] [],
      dsimp ["only"] ["[", "]"] [] [],
      rw [expr dif_pos rfl] [],
      exact [expr neg_add_self _] },
    have [ident hs2] [":", expr «expr = »(s2.weighted_vsub p f, (0 : V))] [],
    { set [] [ident f2] [":", expr ι → V] [":="] [expr λ
       x, «expr • »(f x, «expr -ᵥ »(p x, p i1))] ["with", ident hf2def],
      set [] [ident g2] [":", expr {x // «expr ≠ »(x, i1)} → V] [":="] [expr λ
       x, «expr • »(g x, «expr -ᵥ »(p x, p i1))] ["with", ident hg2def],
      have [ident hf2g2] [":", expr ∀ x : {x // «expr ≠ »(x, i1)}, «expr = »(f2 x, g2 x)] [],
      { simp_rw ["[", expr hf2def, ",", expr hg2def, ",", expr hfg, "]"] [],
        exact [expr λ x, rfl] },
      rw ["[", expr finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s2 f p hf (p i1), ",", expr finset.weighted_vsub_of_point_insert, ",", expr finset.weighted_vsub_of_point_apply, ",", expr finset.sum_subtype_map_embedding (λ
        x hx, hf2g2 x), "]"] [],
      exact [expr hg] },
    exact [expr h s2 f hf hs2 i (finset.mem_insert_of_mem (finset.mem_map.2 ⟨i, hi, rfl⟩))] },
  { intro [ident h],
    rw [expr linear_independent_iff'] ["at", ident h],
    intros [ident s, ident w, ident hw, ident hs, ident i, ident hi],
    rw ["[", expr finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s w p hw (p i1), ",", "<-", expr s.weighted_vsub_of_point_erase w p i1, ",", expr finset.weighted_vsub_of_point_apply, "]"] ["at", ident hs],
    let [ident f] [":", expr ι → V] [":=", expr λ i, «expr • »(w i, «expr -ᵥ »(p i, p i1))],
    have [ident hs2] [":", expr «expr = »(«expr∑ in , »((i), (s.erase i1).subtype (λ i, «expr ≠ »(i, i1)), f i), 0)] [],
    { rw ["[", "<-", expr hs, "]"] [],
      convert [] [expr finset.sum_subtype_of_mem f (λ x, finset.ne_of_mem_erase)] [] },
    have [ident h2] [] [":=", expr h ((s.erase i1).subtype (λ i, «expr ≠ »(i, i1))) (λ x, w x) hs2],
    simp_rw ["[", expr finset.mem_subtype, "]"] ["at", ident h2],
    have [ident h2b] [":", expr ∀
     i «expr ∈ » s, «expr ≠ »(i, i1) → «expr = »(w i, 0)] [":=", expr λ
     i his hi, h2 ⟨i, hi⟩ (finset.mem_erase_of_ne_of_mem hi his)],
    exact [expr finset.eq_zero_of_sum_eq_zero hw h2b i hi] }
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
theorem affine_independent_set_iff_linear_independent_vsub
{s : set P}
{p₁ : P}
(hp₁ : «expr ∈ »(p₁, s)) : «expr ↔ »(affine_independent k (λ
 p, p : s → P), linear_independent k (λ v, v : «expr '' »(λ p, («expr -ᵥ »(p, p₁) : V), «expr \ »(s, {p₁})) → V)) :=
begin
  rw [expr affine_independent_iff_linear_independent_vsub k (λ p, p : s → P) ⟨p₁, hp₁⟩] [],
  split,
  { intro [ident h],
    have [ident hv] [":", expr ∀
     v : «expr '' »(λ
      p, («expr -ᵥ »(p, p₁) : V), «expr \ »(s, {p₁})), «expr ∈ »(«expr +ᵥ »((v : V), p₁), «expr \ »(s, {p₁}))] [":=", expr λ
     v, (vsub_left_injective p₁).mem_set_image.1 «expr ▸ »((vadd_vsub (v : V) p₁).symm, v.property)],
    let [ident f] [":", expr «expr '' »(λ
      p : P, («expr -ᵥ »(p, p₁) : V), «expr \ »(s, {p₁})) → {x : s // «expr ≠ »(x, ⟨p₁, hp₁⟩)}] [":=", expr λ
     x, ⟨⟨«expr +ᵥ »((x : V), p₁), set.mem_of_mem_diff (hv x)⟩, λ
      hx, set.not_mem_of_mem_diff (hv x) (subtype.ext_iff.1 hx)⟩],
    convert [] [expr h.comp f (λ
      x1 x2 hx, subtype.ext (vadd_right_cancel p₁ (subtype.ext_iff.1 (subtype.ext_iff.1 hx))))] [],
    ext [] [ident v] [],
    exact [expr (vadd_vsub (v : V) p₁).symm] },
  { intro [ident h],
    let [ident f] [":", expr {x : s // «expr ≠ »(x, ⟨p₁, hp₁⟩)} → «expr '' »(λ
      p : P, («expr -ᵥ »(p, p₁) : V), «expr \ »(s, {p₁}))] [":=", expr λ
     x, ⟨«expr -ᵥ »(((x : s) : P), p₁), ⟨x, ⟨⟨(x : s).property, λ hx, x.property (subtype.ext hx)⟩, rfl⟩⟩⟩],
    convert [] [expr h.comp f (λ x1 x2 hx, subtype.ext (subtype.ext (vsub_left_cancel (subtype.ext_iff.1 hx))))] [] }
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
theorem linear_independent_set_iff_affine_independent_vadd_union_singleton
{s : set V}
(hs : ∀ v «expr ∈ » s, «expr ≠ »(v, (0 : V)))
(p₁ : P) : «expr ↔ »(linear_independent k (λ
 v, v : s → V), affine_independent k (λ p, p : «expr ∪ »({p₁}, «expr '' »(λ v, «expr +ᵥ »(v, p₁), s)) → P)) :=
begin
  rw [expr affine_independent_set_iff_linear_independent_vsub k (set.mem_union_left _ (set.mem_singleton p₁))] [],
  have [ident h] [":", expr «expr = »(«expr '' »(λ
     p, («expr -ᵥ »(p, p₁) : V), «expr \ »(«expr ∪ »({p₁}, «expr '' »(λ v, «expr +ᵥ »(v, p₁), s)), {p₁})), s)] [],
  { simp_rw ["[", expr set.union_diff_left, ",", expr set.image_diff (vsub_left_injective p₁), ",", expr set.image_image, ",", expr set.image_singleton, ",", expr vsub_self, ",", expr vadd_vsub, ",", expr set.image_id', "]"] [],
    exact [expr set.diff_singleton_eq_self (λ h, hs 0 h rfl)] },
  rw [expr h] []
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `set.indicator`. -/
theorem affine_independent_iff_indicator_eq_of_affine_combination_eq
(p : ι → P) : «expr ↔ »(affine_independent k p, ∀
 (s1 s2 : finset ι)
 (w1
  w2 : ι → k), «expr = »(«expr∑ in , »((i), s1, w1 i), 1) → «expr = »(«expr∑ in , »((i), s2, w2 i), 1) → «expr = »(s1.affine_combination p w1, s2.affine_combination p w2) → «expr = »(set.indicator «expr↑ »(s1) w1, set.indicator «expr↑ »(s2) w2)) :=
begin
  split,
  { intros [ident ha, ident s1, ident s2, ident w1, ident w2, ident hw1, ident hw2, ident heq],
    ext [] [ident i] [],
    by_cases [expr hi, ":", expr «expr ∈ »(i, «expr ∪ »(s1, s2))],
    { rw ["<-", expr sub_eq_zero] [],
      rw [expr set.sum_indicator_subset _ (finset.subset_union_left s1 s2)] ["at", ident hw1],
      rw [expr set.sum_indicator_subset _ (finset.subset_union_right s1 s2)] ["at", ident hw2],
      have [ident hws] [":", expr «expr = »(«expr∑ in , »((i), «expr ∪ »(s1, s2), «expr - »(set.indicator «expr↑ »(s1) w1, set.indicator «expr↑ »(s2) w2) i), 0)] [],
      { simp [] [] [] ["[", expr hw1, ",", expr hw2, "]"] [] [] },
      rw ["[", expr finset.affine_combination_indicator_subset _ _ (finset.subset_union_left s1 s2), ",", expr finset.affine_combination_indicator_subset _ _ (finset.subset_union_right s1 s2), ",", "<-", expr @vsub_eq_zero_iff_eq V, ",", expr finset.affine_combination_vsub, "]"] ["at", ident heq],
      exact [expr ha «expr ∪ »(s1, s2) «expr - »(set.indicator «expr↑ »(s1) w1, set.indicator «expr↑ »(s2) w2) hws heq i hi] },
    { rw ["[", "<-", expr finset.mem_coe, ",", expr finset.coe_union, "]"] ["at", ident hi],
      simp [] [] [] ["[", expr mt (set.mem_union_left «expr↑ »(s2)) hi, ",", expr mt (set.mem_union_right «expr↑ »(s1)) hi, "]"] [] [] } },
  { intros [ident ha, ident s, ident w, ident hw, ident hs, ident i0, ident hi0],
    let [ident w1] [":", expr ι → k] [":=", expr function.update (function.const ι 0) i0 1],
    have [ident hw1] [":", expr «expr = »(«expr∑ in , »((i), s, w1 i), 1)] [],
    { rw ["[", expr finset.sum_update_of_mem hi0, ",", expr finset.sum_const_zero, ",", expr add_zero, "]"] [] },
    have [ident hw1s] [":", expr «expr = »(s.affine_combination p w1, p i0)] [":=", expr s.affine_combination_of_eq_one_of_eq_zero w1 p hi0 (function.update_same _ _ _) (λ
      _ _ hne, function.update_noteq hne _ _)],
    let [ident w2] [] [":=", expr «expr + »(w, w1)],
    have [ident hw2] [":", expr «expr = »(«expr∑ in , »((i), s, w2 i), 1)] [],
    { simp [] [] [] ["[", expr w2, ",", expr finset.sum_add_distrib, ",", expr hw, ",", expr hw1, "]"] [] [] },
    have [ident hw2s] [":", expr «expr = »(s.affine_combination p w2, p i0)] [],
    { simp [] [] [] ["[", expr w2, ",", "<-", expr finset.weighted_vsub_vadd_affine_combination, ",", expr hs, ",", expr hw1s, "]"] [] [] },
    replace [ident ha] [] [":=", expr ha s s w2 w1 hw2 hw1 «expr ▸ »(hw1s.symm, hw2s)],
    have [ident hws] [":", expr «expr = »(«expr - »(w2 i0, w1 i0), 0)] [],
    { rw ["<-", expr finset.mem_coe] ["at", ident hi0],
      rw ["[", "<-", expr set.indicator_of_mem hi0 w2, ",", "<-", expr set.indicator_of_mem hi0 w1, ",", expr ha, ",", expr sub_self, "]"] [] },
    simpa [] [] [] ["[", expr w2, "]"] [] ["using", expr hws] }
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
theorem affine_independent_iff_eq_of_fintype_affine_combination_eq
[fintype ι]
(p : ι → P) : «expr ↔ »(affine_independent k p, ∀
 w1
 w2 : ι → k, «expr = »(«expr∑ , »((i), w1 i), 1) → «expr = »(«expr∑ , »((i), w2 i), 1) → «expr = »(finset.univ.affine_combination p w1, finset.univ.affine_combination p w2) → «expr = »(w1, w2)) :=
begin
  rw [expr affine_independent_iff_indicator_eq_of_affine_combination_eq] [],
  split,
  { intros [ident h, ident w1, ident w2, ident hw1, ident hw2, ident hweq],
    simpa [] [] ["only"] ["[", expr set.indicator_univ, ",", expr finset.coe_univ, "]"] [] ["using", expr h _ _ w1 w2 hw1 hw2 hweq] },
  { intros [ident h, ident s1, ident s2, ident w1, ident w2, ident hw1, ident hw2, ident hweq],
    have [ident hw1'] [":", expr «expr = »(«expr∑ , »((i), (s1 : set ι).indicator w1 i), 1)] [],
    { rwa [expr set.sum_indicator_subset _ (finset.subset_univ s1)] ["at", ident hw1] },
    have [ident hw2'] [":", expr «expr = »(«expr∑ , »((i), (s2 : set ι).indicator w2 i), 1)] [],
    { rwa [expr set.sum_indicator_subset _ (finset.subset_univ s2)] ["at", ident hw2] },
    rw ["[", expr finset.affine_combination_indicator_subset w1 p (finset.subset_univ s1), ",", expr finset.affine_combination_indicator_subset w2 p (finset.subset_univ s2), "]"] ["at", ident hweq],
    exact [expr h _ _ hw1' hw2' hweq] }
end

variable {k}

/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `linear_independent.units_smul`. -/
theorem AffineIndependent.units_line_map {p : ι → P} (hp : AffineIndependent k p) (j : ι) (w : ι → Units k) :
  AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) :=
  by 
    rw [affine_independent_iff_linear_independent_vsub k _ j] at hp⊢
    simp only [AffineMap.line_map_vsub_left, AffineMap.coe_const, AffineMap.line_map_same]
    exact hp.units_smul fun i => w i

theorem AffineIndependent.indicator_eq_of_affine_combination_eq {p : ι → P} (ha : AffineIndependent k p)
  (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : (∑i in s₁, w₁ i) = 1) (hw₂ : (∑i in s₂, w₂ i) = 1)
  (h : s₁.affine_combination p w₁ = s₂.affine_combination p w₂) :
  Set.indicator («expr↑ » s₁) w₁ = Set.indicator («expr↑ » s₂) w₂ :=
  (affine_independent_iff_indicator_eq_of_affine_combination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) :
  Function.Injective p :=
  by 
    intro i j hij 
    rw [affine_independent_iff_linear_independent_vsub _ _ j] at ha 
    byContra hij' 
    exact ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr hij)

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
theorem affine_independent.comp_embedding
{ι2 : Type*}
(f : «expr ↪ »(ι2, ι))
{p : ι → P}
(ha : affine_independent k p) : affine_independent k «expr ∘ »(p, f) :=
begin
  intros [ident fs, ident w, ident hw, ident hs, ident i0, ident hi0],
  let [ident fs'] [] [":=", expr fs.map f],
  let [ident w'] [] [":=", expr λ i, if h : «expr∃ , »((i2), «expr = »(f i2, i)) then w h.some else 0],
  have [ident hw'] [":", expr ∀ i2 : ι2, «expr = »(w' (f i2), w i2)] [],
  { intro [ident i2],
    have [ident h] [":", expr «expr∃ , »((i : ι2), «expr = »(f i, f i2))] [":=", expr ⟨i2, rfl⟩],
    have [ident hs] [":", expr «expr = »(h.some, i2)] [":=", expr f.injective h.some_spec],
    simp_rw ["[", expr w', ",", expr dif_pos h, ",", expr hs, "]"] [] },
  have [ident hw's] [":", expr «expr = »(«expr∑ in , »((i), fs', w' i), 0)] [],
  { rw ["[", "<-", expr hw, ",", expr finset.sum_map, "]"] [],
    simp [] [] [] ["[", expr hw', "]"] [] [] },
  have [ident hs'] [":", expr «expr = »(fs'.weighted_vsub p w', (0 : V))] [],
  { rw ["[", "<-", expr hs, ",", expr finset.weighted_vsub_map, "]"] [],
    congr' [] ["with", ident i],
    simp [] [] [] ["[", expr hw', "]"] [] [] },
  rw ["[", "<-", expr ha fs' w' hw's hs' (f i0) ((finset.mem_map' _).2 hi0), ",", expr hw', "]"] []
end

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
protected theorem AffineIndependent.subtype {p : ι → P} (ha : AffineIndependent k p) (s : Set ι) :
  AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (embedding.subtype _)

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected
theorem affine_independent.range
{p : ι → P}
(ha : affine_independent k p) : affine_independent k (λ x, x : set.range p → P) :=
begin
  let [ident f] [":", expr set.range p → ι] [":=", expr λ x, x.property.some],
  have [ident hf] [":", expr ∀ x, «expr = »(p (f x), x)] [":=", expr λ x, x.property.some_spec],
  let [ident fe] [":", expr «expr ↪ »(set.range p, ι)] [":=", expr ⟨f, λ
    x₁ x₂ he, subtype.ext «expr ▸ »(hf x₁, «expr ▸ »(hf x₂, «expr ▸ »(he, rfl)))⟩],
  convert [] [expr ha.comp_embedding fe] [],
  ext [] [] [],
  simp [] [] [] ["[", expr hf, "]"] [] []
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem affine_independent_equiv
{ι' : Type*}
(e : «expr ≃ »(ι, ι'))
{p : ι' → P} : «expr ↔ »(affine_independent k «expr ∘ »(p, e), affine_independent k p) :=
begin
  refine [expr ⟨_, affine_independent.comp_embedding e.to_embedding⟩],
  intros [ident h],
  have [] [":", expr «expr = »(p, «expr ∘ »(p, «expr ∘ »(e, e.symm.to_embedding)))] [],
  { ext [] [] [],
    simp [] [] [] [] [] [] },
  rw [expr this] [],
  exact [expr h.comp_embedding e.symm.to_embedding]
end

/-- If a set of points is affinely independent, so is any subset. -/
protected theorem AffineIndependent.mono {s t : Set P} (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
  AffineIndependent k (fun x => x : s → P) :=
  ha.comp_embedding (s.embedding_of_subset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
theorem AffineIndependent.of_set_of_injective {p : ι → P} (ha : AffineIndependent k (fun x => x : Set.Range p → P))
  (hi : Function.Injective p) : AffineIndependent k p :=
  ha.comp_embedding (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ : ι ↪ Set.Range p)

section Composition

variable {V₂ P₂ : Type _} [AddCommGroupₓ V₂] [Module k V₂] [affine_space V₂ P₂]

include V₂

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
theorem affine_independent.of_comp
{p : ι → P}
(f : «expr →ᵃ[ ] »(P, k, P₂))
(hai : affine_independent k «expr ∘ »(f, p)) : affine_independent k p :=
begin
  cases [expr is_empty_or_nonempty ι] ["with", ident h, ident h],
  { haveI [] [] [":=", expr h],
    apply [expr affine_independent_of_subsingleton] },
  obtain ["⟨", ident i, "⟩", ":=", expr h],
  rw [expr affine_independent_iff_linear_independent_vsub k p i] [],
  simp_rw ["[", expr affine_independent_iff_linear_independent_vsub k «expr ∘ »(f, p) i, ",", expr function.comp_app, ",", "<-", expr f.linear_map_vsub, "]"] ["at", ident hai],
  exact [expr linear_independent.of_comp f.linear hai]
end

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
theorem affine_independent.map'
{p : ι → P}
(hai : affine_independent k p)
(f : «expr →ᵃ[ ] »(P, k, P₂))
(hf : function.injective f) : affine_independent k «expr ∘ »(f, p) :=
begin
  cases [expr is_empty_or_nonempty ι] ["with", ident h, ident h],
  { haveI [] [] [":=", expr h],
    apply [expr affine_independent_of_subsingleton] },
  obtain ["⟨", ident i, "⟩", ":=", expr h],
  rw [expr affine_independent_iff_linear_independent_vsub k p i] ["at", ident hai],
  simp_rw ["[", expr affine_independent_iff_linear_independent_vsub k «expr ∘ »(f, p) i, ",", expr function.comp_app, ",", "<-", expr f.linear_map_vsub, "]"] [],
  have [ident hf'] [":", expr «expr = »(f.linear.ker, «expr⊥»())] [],
  { rwa ["[", expr linear_map.ker_eq_bot, ",", expr f.injective_iff_linear_injective, "]"] [] },
  exact [expr linear_independent.map' hai f.linear hf']
end

/-- Injective affine maps preserve affine independence. -/
theorem AffineMap.affine_independent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
  AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

/-- Affine equivalences preserve affine independence of families of points. -/
theorem AffineEquiv.affine_independent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
  AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.to_affine_map.affine_independent_iff e.to_equiv.injective

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Affine equivalences preserve affine independence of subsets. -/
theorem affine_equiv.affine_independent_set_of_eq_iff
{s : set P}
(e : «expr ≃ᵃ[ ] »(P, k, P₂)) : «expr ↔ »(affine_independent k (coe : «expr '' »(e, s) → P₂), affine_independent k (coe : s → P)) :=
begin
  have [] [":", expr «expr = »(«expr ∘ »(e, (coe : s → P)), «expr ∘ »((coe : «expr '' »(e, s) → P₂), (e : «expr ≃ »(P, P₂)).image s))] [":=", expr rfl],
  rw ["[", "<-", expr e.affine_independent_iff, ",", expr this, ",", expr affine_independent_equiv, "]"] []
end

end Composition

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
theorem affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span
[nontrivial k]
{p : ι → P}
(ha : affine_independent k p)
{s1 s2 : set ι}
{p0 : P}
(hp0s1 : «expr ∈ »(p0, affine_span k «expr '' »(p, s1)))
(hp0s2 : «expr ∈ »(p0, affine_span k «expr '' »(p, s2))) : «expr∃ , »((i : ι), «expr ∈ »(i, «expr ∩ »(s1, s2))) :=
begin
  rw [expr set.image_eq_range] ["at", ident hp0s1, ident hp0s2],
  rw ["[", expr mem_affine_span_iff_eq_affine_combination, ",", "<-", expr finset.eq_affine_combination_subset_iff_eq_affine_combination_subtype, "]"] ["at", ident hp0s1, ident hp0s2],
  rcases [expr hp0s1, "with", "⟨", ident fs1, ",", ident hfs1, ",", ident w1, ",", ident hw1, ",", ident hp0s1, "⟩"],
  rcases [expr hp0s2, "with", "⟨", ident fs2, ",", ident hfs2, ",", ident w2, ",", ident hw2, ",", ident hp0s2, "⟩"],
  rw [expr affine_independent_iff_indicator_eq_of_affine_combination_eq] ["at", ident ha],
  replace [ident ha] [] [":=", expr ha fs1 fs2 w1 w2 hw1 hw2 «expr ▸ »(hp0s1, hp0s2)],
  have [ident hnz] [":", expr «expr ≠ »(«expr∑ in , »((i), fs1, w1 i), 0)] [":=", expr «expr ▸ »(hw1.symm, one_ne_zero)],
  rcases [expr finset.exists_ne_zero_of_sum_ne_zero hnz, "with", "⟨", ident i, ",", ident hifs1, ",", ident hinz, "⟩"],
  simp_rw ["[", "<-", expr set.indicator_of_mem (finset.mem_coe.2 hifs1) w1, ",", expr ha, "]"] ["at", ident hinz],
  use ["[", expr i, ",", expr hfs1 hifs1, ",", expr hfs2 (set.mem_of_indicator_ne_zero hinz), "]"]
end

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.affine_span_disjoint_of_disjoint [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p)
  {s1 s2 : Set ι} (hd : s1 ∩ s2 = ∅) : (affineSpan k (p '' s1) : Set P) ∩ affineSpan k (p '' s2) = ∅ :=
  by 
    byContra hne 
    change (affineSpan k (p '' s1) : Set P) ∩ affineSpan k (p '' s2) ≠ ∅ at hne 
    rw [Set.ne_empty_iff_nonempty] at hne 
    rcases hne with ⟨p0, hp0s1, hp0s2⟩
    cases' ha.exists_mem_inter_of_exists_mem_inter_affine_span hp0s1 hp0s2 with i hi 
    exact Set.not_mem_empty i (hd ▸ hi)

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
protected
theorem affine_independent.mem_affine_span_iff
[nontrivial k]
{p : ι → P}
(ha : affine_independent k p)
(i : ι)
(s : set ι) : «expr ↔ »(«expr ∈ »(p i, affine_span k «expr '' »(p, s)), «expr ∈ »(i, s)) :=
begin
  split,
  { intro [ident hs],
    have [ident h] [] [":=", expr affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span ha hs (mem_affine_span k (set.mem_image_of_mem _ (set.mem_singleton _)))],
    rwa ["[", "<-", expr set.nonempty_def, ",", expr set.inter_singleton_nonempty, "]"] ["at", ident h] },
  { exact [expr λ h, mem_affine_span k (set.mem_image_of_mem p h)] }
end

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
theorem AffineIndependent.not_mem_affine_span_diff [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) (i : ι)
  (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) :=
  by 
    simp [ha]

theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V} (h : ¬AffineIndependent k (coeₓ : t → V)) :
  ∃ f : V → k, (∑e in t, f e • e) = 0 ∧ (∑e in t, f e) = 0 ∧ ∃ (x : _)(_ : x ∈ t), f x ≠ 0 :=
  by 
    classical 
    rw [affine_independent_iff_of_fintype] at h 
    simp only [exists_prop, not_forall] at h 
    obtain ⟨w, hw, hwt, i, hi⟩ := h 
    simp only [Finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ w (coeₓ : t → V) hw 0, vsub_eq_sub,
      Finset.weighted_vsub_of_point_apply, sub_zero] at hwt 
    let f : ∀ x : V, x ∈ t → k := fun x hx => w ⟨x, hx⟩
    refine'
      ⟨fun x => if hx : x ∈ t then f x hx else (0 : k), _, _,
        by 
          use i 
          simp [hi, f]⟩
    suffices  : (∑e : V in t, dite (e ∈ t) (fun hx => f e hx • e) fun hx => 0) = 0
    ·
      convert this 
      ext 
      byCases' hx : x ∈ t <;> simp [hx]
    all_goals 
      simp only [Finset.sum_dite_of_true fun x h => h, Subtype.val_eq_coe, Finset.mk_coe, f, hwt, hw]

end AffineIndependent

section DivisionRing

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _}

include V

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
theorem exists_subset_affine_independent_affine_span_eq_top
{s : set P}
(h : affine_independent k (λ
 p, p : s → P)) : «expr∃ , »((t : set P), «expr ∧ »(«expr ⊆ »(s, t), «expr ∧ »(affine_independent k (λ
   p, p : t → P), «expr = »(affine_span k t, «expr⊤»())))) :=
begin
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", "⟨", ident p₁, ",", ident hp₁, "⟩"],
  { have [ident p₁] [":", expr P] [":=", expr add_torsor.nonempty.some],
    let [ident hsv] [] [":=", expr basis.of_vector_space k V],
    have [ident hsvi] [] [":=", expr hsv.linear_independent],
    have [ident hsvt] [] [":=", expr hsv.span_eq],
    rw [expr basis.coe_of_vector_space] ["at", ident hsvi, ident hsvt],
    have [ident h0] [":", expr ∀ v : V, «expr ∈ »(v, basis.of_vector_space_index _ _) → «expr ≠ »(v, 0)] [],
    { intros [ident v, ident hv],
      simpa [] [] [] [] [] ["using", expr hsv.ne_zero ⟨v, hv⟩] },
    rw [expr linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁] ["at", ident hsvi],
    exact [expr ⟨«expr ∪ »({p₁}, «expr '' »(λ
        v, «expr +ᵥ »(v, p₁), _)), set.empty_subset _, hsvi, affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩] },
  { rw [expr affine_independent_set_iff_linear_independent_vsub k hp₁] ["at", ident h],
    let [ident bsv] [] [":=", expr basis.extend h],
    have [ident hsvi] [] [":=", expr bsv.linear_independent],
    have [ident hsvt] [] [":=", expr bsv.span_eq],
    rw [expr basis.coe_extend] ["at", ident hsvi, ident hsvt],
    have [ident hsv] [] [":=", expr h.subset_extend (set.subset_univ _)],
    have [ident h0] [":", expr ∀ v : V, «expr ∈ »(v, h.extend _) → «expr ≠ »(v, 0)] [],
    { intros [ident v, ident hv],
      simpa [] [] [] [] [] ["using", expr bsv.ne_zero ⟨v, hv⟩] },
    rw [expr linear_independent_set_iff_affine_independent_vadd_union_singleton k h0 p₁] ["at", ident hsvi],
    refine [expr ⟨«expr ∪ »({p₁}, «expr '' »(λ v, «expr +ᵥ »(v, p₁), h.extend (set.subset_univ _))), _, _⟩],
    { refine [expr set.subset.trans _ (set.union_subset_union_right _ (set.image_subset _ hsv))],
      simp [] [] [] ["[", expr set.image_image, "]"] [] [] },
    { use ["[", expr hsvi, ",", expr affine_span_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt, "]"] } }
end

variable (k V)

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_affine_independent
(s : set P) : «expr∃ , »((t «expr ⊆ » s), «expr ∧ »(«expr = »(affine_span k t, affine_span k s), affine_independent k (coe : t → P))) :=
begin
  rcases [expr s.eq_empty_or_nonempty, "with", ident rfl, "|", "⟨", ident p, ",", ident hp, "⟩"],
  { exact [expr ⟨«expr∅»(), set.empty_subset «expr∅»(), rfl, affine_independent_of_subsingleton k _⟩] },
  obtain ["⟨", ident b, ",", ident hb₁, ",", ident hb₂, ",", ident hb₃, "⟩", ":=", expr exists_linear_independent k «expr '' »((equiv.vadd_const p).symm, s)],
  have [ident hb₀] [":", expr ∀ v : V, «expr ∈ »(v, b) → «expr ≠ »(v, 0)] [],
  { exact [expr λ v hv, hb₃.ne_zero (⟨v, hv⟩ : b)] },
  rw [expr linear_independent_set_iff_affine_independent_vadd_union_singleton k hb₀ p] ["at", ident hb₃],
  refine [expr ⟨«expr ∪ »({p}, «expr '' »(equiv.vadd_const p, b)), _, _, hb₃⟩],
  { apply [expr set.union_subset (set.singleton_subset_iff.mpr hp)],
    rwa ["<-", expr (equiv.vadd_const p).subset_image' b s] [] },
  { rw ["[", expr equiv.coe_vadd_const_symm, ",", "<-", expr vector_span_eq_span_vsub_set_right k hp, "]"] ["at", ident hb₂],
    apply [expr affine_subspace.ext_of_direction_eq],
    { have [] [":", expr «expr = »(submodule.span k b, submodule.span k (insert 0 b))] [],
      { by simp [] [] [] [] [] [] },
      simp [] [] ["only"] ["[", expr direction_affine_span, ",", "<-", expr hb₂, ",", expr equiv.coe_vadd_const, ",", expr set.singleton_union, ",", expr vector_span_eq_span_vsub_set_right k (set.mem_insert p _), ",", expr this, "]"] [] [],
      congr,
      change [expr «expr = »(«expr '' »((equiv.vadd_const p).symm, insert p «expr '' »(equiv.vadd_const p, b)), _)] [] [],
      rw ["[", expr set.image_insert_eq, ",", "<-", expr set.image_comp, "]"] [],
      simp [] [] [] [] [] [] },
    { use [expr p],
      simp [] [] ["only"] ["[", expr equiv.coe_vadd_const, ",", expr set.singleton_union, ",", expr set.mem_inter_eq, ",", expr coe_affine_span, "]"] [] [],
      exact [expr ⟨mem_span_points k _ _ (set.mem_insert p _), mem_span_points k _ _ hp⟩] } }
end

variable (k) {V P}

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:341:40: in rw: ././Mathport/Syntax/Translate/Basic.lean:558:61: unsupported notation `«expr![ , ]»
/-- Two different points are affinely independent. -/
theorem affine_independent_of_ne {p₁ p₂ : P} (h : «expr ≠ »(p₁, p₂)) : affine_independent k «expr![ , ]»([p₁, p₂]) :=
begin
  rw [expr affine_independent_iff_linear_independent_vsub k «expr![ , ]»([p₁, p₂]) 0] [],
  let [ident i₁] [":", expr {x // «expr ≠ »(x, (0 : fin 2))}] [":=", expr ⟨1, by norm_num [] []⟩],
  have [ident he'] [":", expr ∀ i, «expr = »(i, i₁)] [],
  { rintro ["⟨", ident i, ",", ident hi, "⟩"],
    ext [] [] [],
    fin_cases [ident i] [],
    { simpa [] [] [] [] [] ["using", expr hi] } },
  haveI [] [":", expr unique {x // «expr ≠ »(x, (0 : fin 2))}] [":=", expr ⟨⟨i₁⟩, he'⟩],
  have [ident hz] [":", expr «expr ≠ »((«expr -ᵥ »(«expr![ , ]»([p₁, p₂]) «expr↑ »(default {x // «expr ≠ »(x, (0 : fin 2))}), «expr![ , ]»([p₁, p₂]) 0) : V), 0)] [],
  { rw [expr he' (default _)] [],
    simp [] [] [] [] [] [],
    cc },
  exact [expr linear_independent_unique _ hz]
end

end DivisionRing

namespace Affine

variable (k : Type _) {V : Type _} (P : Type _) [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P]

include V

/-- A `simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure simplex (n : ℕ) where 
  points : Finₓ (n+1) → P 
  Independent : AffineIndependent k points

/-- A `triangle k P` is a collection of three affinely independent points. -/
abbrev triangle :=
  simplex k P 2

namespace Simplex

variable {P}

/-- Construct a 0-simplex from a point. -/
def mk_of_point (p : P) : simplex k P 0 :=
  ⟨fun _ => p, affine_independent_of_subsingleton k _⟩

/-- The point in a simplex constructed with `mk_of_point`. -/
@[simp]
theorem mk_of_point_points (p : P) (i : Finₓ 1) : (mk_of_point k p).points i = p :=
  rfl

instance [Inhabited P] : Inhabited (simplex k P 0) :=
  ⟨mk_of_point k$ default P⟩

instance Nonempty : Nonempty (simplex k P 0) :=
  ⟨mk_of_point k$ AddTorsor.nonempty.some⟩

variable {k V}

/-- Two simplices are equal if they have the same points. -/
@[ext]
theorem ext {n : ℕ} {s1 s2 : simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 :=
  by 
    cases s1 
    cases s2 
    congr with i 
    exact h i

/-- Two simplices are equal if and only if they have the same points. -/
theorem ext_iff {n : ℕ} (s1 s2 : simplex k P n) : s1 = s2 ↔ ∀ i, s1.points i = s2.points i :=
  ⟨fun h _ => h ▸ rfl, ext⟩

/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {n : ℕ} (s : simplex k P n) {fs : Finset (Finₓ (n+1))} {m : ℕ} (h : fs.card = m+1) : simplex k P m :=
  ⟨s.points ∘ fs.order_emb_of_fin h, s.independent.comp_embedding (fs.order_emb_of_fin h).toEmbedding⟩

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points {n : ℕ} (s : simplex k P n) {fs : Finset (Finₓ (n+1))} {m : ℕ} (h : fs.card = m+1)
  (i : Finₓ (m+1)) : (s.face h).points i = s.points (fs.order_emb_of_fin h i) :=
  rfl

/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points' {n : ℕ} (s : simplex k P n) {fs : Finset (Finₓ (n+1))} {m : ℕ} (h : fs.card = m+1) :
  (s.face h).points = s.points ∘ fs.order_emb_of_fin h :=
  rfl

/-- A single-point face equals the 0-simplex constructed with
`mk_of_point`. -/
@[simp]
theorem face_eq_mk_of_point {n : ℕ} (s : simplex k P n) (i : Finₓ (n+1)) :
  s.face (Finset.card_singleton i) = mk_of_point k (s.points i) :=
  by 
    ext 
    simp [face_points]

/-- The set of points of a face. -/
@[simp]
theorem range_face_points {n : ℕ} (s : simplex k P n) {fs : Finset (Finₓ (n+1))} {m : ℕ} (h : fs.card = m+1) :
  Set.Range (s.face h).points = s.points '' «expr↑ » fs :=
  by 
    rw [face_points', Set.range_comp, Finset.range_order_emb_of_fin]

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

include V

/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp]
theorem face_centroid_eq_centroid {n : ℕ} (s : simplex k P n) {fs : Finset (Finₓ (n+1))} {m : ℕ} (h : fs.card = m+1) :
  Finset.univ.centroid k (s.face h).points = fs.centroid k s.points :=
  by 
    convert (finset.univ.centroid_map k (fs.order_emb_of_fin h).toEmbedding s.points).symm 
    rw [←Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
    simp 

-- error in LinearAlgebra.AffineSpace.Independent: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
theorem centroid_eq_iff
[char_zero k]
{n : exprℕ()}
(s : simplex k P n)
{fs₁ fs₂ : finset (fin «expr + »(n, 1))}
{m₁ m₂ : exprℕ()}
(h₁ : «expr = »(fs₁.card, «expr + »(m₁, 1)))
(h₂ : «expr = »(fs₂.card, «expr + »(m₂, 1))) : «expr ↔ »(«expr = »(fs₁.centroid k s.points, fs₂.centroid k s.points), «expr = »(fs₁, fs₂)) :=
begin
  split,
  { intro [ident h],
    rw ["[", expr finset.centroid_eq_affine_combination_fintype, ",", expr finset.centroid_eq_affine_combination_fintype, "]"] ["at", ident h],
    have [ident ha] [] [":=", expr (affine_independent_iff_indicator_eq_of_affine_combination_eq k s.points).1 s.independent _ _ _ _ (fs₁.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₁) (fs₂.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₂) h],
    simp_rw ["[", expr finset.coe_univ, ",", expr set.indicator_univ, ",", expr function.funext_iff, ",", expr finset.centroid_weights_indicator_def, ",", expr finset.centroid_weights, ",", expr h₁, ",", expr h₂, "]"] ["at", ident ha],
    ext [] [ident i] [],
    replace [ident ha] [] [":=", expr ha i],
    split,
    all_goals { intro [ident hi],
      by_contradiction [ident hni],
      simp [] [] [] ["[", expr hi, ",", expr hni, "]"] [] ["at", ident ha],
      norm_cast ["at", ident ha] } },
  { intro [ident h],
    have [ident hm] [":", expr «expr = »(m₁, m₂)] [],
    { subst [expr h],
      simpa [] [] [] ["[", expr h₁, "]"] [] ["using", expr h₂] },
    subst [expr hm],
    congr,
    exact [expr h] }
end

/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
theorem face_centroid_eq_iff [CharZero k] {n : ℕ} (s : simplex k P n) {fs₁ fs₂ : Finset (Finₓ (n+1))} {m₁ m₂ : ℕ}
  (h₁ : fs₁.card = m₁+1) (h₂ : fs₂.card = m₂+1) :
  Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).points ↔ fs₁ = fs₂ :=
  by 
    rw [face_centroid_eq_centroid, face_centroid_eq_centroid]
    exact s.centroid_eq_iff h₁ h₂

/-- Two simplices with the same points have the same centroid. -/
theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : simplex k P n} (h : Set.Range s₁.points = Set.Range s₂.points) :
  Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points :=
  by 
    rw [←Set.image_univ, ←Set.image_univ, ←Finset.coe_univ] at h 
    exact
      finset.univ.centroid_eq_of_inj_on_of_image_eq k _
        (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
        (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h

end Simplex

end Affine

