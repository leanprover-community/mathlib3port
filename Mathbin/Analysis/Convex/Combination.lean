import Mathbin.Algebra.BigOperators.Order 
import Mathbin.Analysis.Convex.Hull 
import Mathbin.LinearAlgebra.AffineSpace.BarycentricCoords

/-!
# Convex combinations

This file defines convex combinations of points in a vector space.

## Main declarations

* `finset.center_mass`: Center of mass of a finite family of points.

## Implementation notes

We divide by the sum of the weights in the definition of `finset.center_mass` because of the way
mathematical arguments go: one doesn't change weights, but merely adds some. This also makes a few
lemmas unconditional on the sum of the weights being `1`.
-/


open Set

open_locale BigOperators Classical

universe u u'

variable{R E F ι ι' : Type _}[LinearOrderedField R][AddCommGroupₓ E][AddCommGroupₓ F][Module R E][Module R F]{s : Set E}

/-- Center of mass of a finite collection of points with prescribed weights.
Note that we require neither `0 ≤ w i` nor `∑ w = 1`. -/
def Finset.centerMass (t : Finset ι) (w : ι → R) (z : ι → E) : E :=
  (∑i in t, w i)⁻¹ • ∑i in t, w i • z i

variable(i j : ι)(c : R)(t : Finset ι)(w : ι → R)(z : ι → E)

open Finset

theorem Finset.center_mass_empty : (∅ : Finset ι).centerMass w z = 0 :=
  by 
    simp only [center_mass, sum_empty, smul_zero]

theorem Finset.center_mass_pair (hne : i ≠ j) :
  ({i, j} : Finset ι).centerMass w z = ((w i / w i+w j) • z i)+(w j / w i+w j) • z j :=
  by 
    simp only [center_mass, sum_pair hne, smul_add, (mul_smul _ _ _).symm, div_eq_inv_mul]

variable{w}

theorem Finset.center_mass_insert (ha : i ∉ t) (hw : (∑j in t, w j) ≠ 0) :
  (insert i t).centerMass w z =
    ((w i / w i+∑j in t, w j) • z i)+((∑j in t, w j) / w i+∑j in t, w j) • t.center_mass w z :=
  by 
    simp only [center_mass, sum_insert ha, smul_add, (mul_smul _ _ _).symm, ←div_eq_inv_mul]
    congr 2
    rw [div_mul_eq_mul_div, mul_inv_cancel hw, one_div]

theorem Finset.center_mass_singleton (hw : w i ≠ 0) : ({i} : Finset ι).centerMass w z = z i :=
  by 
    rw [center_mass, sum_singleton, sum_singleton, ←mul_smul, inv_mul_cancel hw, one_smul]

theorem Finset.center_mass_eq_of_sum_1 (hw : (∑i in t, w i) = 1) : t.center_mass w z = ∑i in t, w i • z i :=
  by 
    simp only [Finset.centerMass, hw, inv_one, one_smul]

theorem Finset.center_mass_smul : (t.center_mass w fun i => c • z i) = c • t.center_mass w z :=
  by 
    simp only [Finset.centerMass, Finset.smul_sum, (mul_smul _ _ _).symm, mul_commₓ c, mul_assocₓ]

/-- A convex combination of two centers of mass is a center of mass as well. This version
deals with two different index types. -/
theorem Finset.center_mass_segment' (s : Finset ι) (t : Finset ι') (ws : ι → R) (zs : ι → E) (wt : ι' → R) (zt : ι' → E)
  (hws : (∑i in s, ws i) = 1) (hwt : (∑i in t, wt i) = 1) (a b : R) (hab : (a+b) = 1) :
  ((a • s.center_mass ws zs)+b • t.center_mass wt zt) =
    (s.map Function.Embedding.inl ∪ t.map Function.Embedding.inr).centerMass
      (Sum.elim (fun i => a*ws i) fun j => b*wt j) (Sum.elim zs zt) :=
  by 
    rw [s.center_mass_eq_of_sum_1 _ hws, t.center_mass_eq_of_sum_1 _ hwt, smul_sum, smul_sum, ←Finset.sum_sum_elim,
      Finset.center_mass_eq_of_sum_1]
    ·
      congr with ⟨⟩ <;> simp only [Sum.elim_inl, Sum.elim_inr, mul_smul]
    ·
      rw [sum_sum_elim, ←mul_sum, ←mul_sum, hws, hwt, mul_oneₓ, mul_oneₓ, hab]

/-- A convex combination of two centers of mass is a center of mass as well. This version
works if two centers of mass share the set of original points. -/
theorem Finset.center_mass_segment (s : Finset ι) (w₁ w₂ : ι → R) (z : ι → E) (hw₁ : (∑i in s, w₁ i) = 1)
  (hw₂ : (∑i in s, w₂ i) = 1) (a b : R) (hab : (a+b) = 1) :
  ((a • s.center_mass w₁ z)+b • s.center_mass w₂ z) = s.center_mass (fun i => (a*w₁ i)+b*w₂ i) z :=
  have hw : (∑i in s, (a*w₁ i)+b*w₂ i) = 1 :=
    by 
      simp only [mul_sum.symm, sum_add_distrib, mul_oneₓ]
  by 
    simp only [Finset.center_mass_eq_of_sum_1, smul_sum, sum_add_distrib, add_smul, mul_smul]

theorem Finset.center_mass_ite_eq (hi : i ∈ t) : t.center_mass (fun j => if i = j then (1 : R) else 0) z = z i :=
  by 
    rw [Finset.center_mass_eq_of_sum_1]
    trans ∑j in t, if i = j then z i else 0
    ·
      congr with i 
      splitIfs 
      exacts[h ▸ one_smul _ _, zero_smul _ _]
    ·
      rw [sum_ite_eq, if_pos hi]
    ·
      rw [sum_ite_eq, if_pos hi]

variable{t w}

theorem Finset.center_mass_subset {t' : Finset ι} (ht : t ⊆ t') (h : ∀ i (_ : i ∈ t'), i ∉ t → w i = 0) :
  t.center_mass w z = t'.center_mass w z :=
  by 
    rw [center_mass, sum_subset ht h, smul_sum, center_mass, smul_sum]
    apply sum_subset ht 
    intro i hit' hit 
    rw [h i hit' hit, zero_smul, smul_zero]

theorem Finset.center_mass_filter_ne_zero : (t.filter fun i => w i ≠ 0).centerMass w z = t.center_mass w z :=
  Finset.center_mass_subset z (filter_subset _ _)$
    fun i hit hit' =>
      by 
        simpa only [hit, mem_filter, true_andₓ, Ne.def, not_not] using hit'

variable{z}

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The center of mass of a finite subset of a convex set belongs to the set
provided that all weights are non-negative, and the total weight is positive. -/
theorem convex.center_mass_mem
(hs : convex R s) : ∀
i «expr ∈ » t, «expr ≤ »(0, w i) → «expr < »(0, «expr∑ in , »((i), t, w i)) → ∀
i «expr ∈ » t, «expr ∈ »(z i, s) → «expr ∈ »(t.center_mass w z, s) :=
begin
  induction [expr t] ["using", ident finset.induction] ["with", ident i, ident t, ident hi, ident ht] [],
  { simp [] [] [] ["[", expr lt_irrefl, "]"] [] [] },
  intros [ident h₀, ident hpos, ident hmem],
  have [ident zi] [":", expr «expr ∈ »(z i, s)] [],
  from [expr hmem _ (mem_insert_self _ _)],
  have [ident hs₀] [":", expr ∀ j «expr ∈ » t, «expr ≤ »(0, w j)] [],
  from [expr λ j hj, «expr $ »(h₀ j, mem_insert_of_mem hj)],
  rw ["[", expr sum_insert hi, "]"] ["at", ident hpos],
  by_cases [expr hsum_t, ":", expr «expr = »(«expr∑ in , »((j), t, w j), 0)],
  { have [ident ws] [":", expr ∀ j «expr ∈ » t, «expr = »(w j, 0)] [],
    from [expr (sum_eq_zero_iff_of_nonneg hs₀).1 hsum_t],
    have [ident wz] [":", expr «expr = »(«expr∑ in , »((j), t, «expr • »(w j, z j)), 0)] [],
    from [expr sum_eq_zero (λ i hi, by simp [] [] [] ["[", expr ws i hi, "]"] [] [])],
    simp [] [] ["only"] ["[", expr center_mass, ",", expr sum_insert hi, ",", expr wz, ",", expr hsum_t, ",", expr add_zero, "]"] [] [],
    simp [] [] ["only"] ["[", expr hsum_t, ",", expr add_zero, "]"] [] ["at", ident hpos],
    rw ["[", "<-", expr mul_smul, ",", expr inv_mul_cancel (ne_of_gt hpos), ",", expr one_smul, "]"] [],
    exact [expr zi] },
  { rw ["[", expr finset.center_mass_insert _ _ _ hi hsum_t, "]"] [],
    refine [expr convex_iff_div.1 hs zi (ht hs₀ _ _) _ (sum_nonneg hs₀) hpos],
    { exact [expr lt_of_le_of_ne (sum_nonneg hs₀) (ne.symm hsum_t)] },
    { intros [ident j, ident hj],
      exact [expr hmem j (mem_insert_of_mem hj)] },
    { exact [expr h₀ _ (mem_insert_self _ _)] } }
end

theorem Convex.sum_mem (hs : Convex R s) (h₀ : ∀ i (_ : i ∈ t), 0 ≤ w i) (h₁ : (∑i in t, w i) = 1)
  (hz : ∀ i (_ : i ∈ t), z i ∈ s) : (∑i in t, w i • z i) ∈ s :=
  by 
    simpa only [h₁, center_mass, inv_one, one_smul] using hs.center_mass_mem h₀ (h₁.symm ▸ zero_lt_one) hz

theorem convex_iff_sum_mem :
  Convex R s ↔
    ∀ (t : Finset E) (w : E → R),
      (∀ i (_ : i ∈ t), 0 ≤ w i) → (∑i in t, w i) = 1 → (∀ x (_ : x ∈ t), x ∈ s) → (∑x in t, w x • x) ∈ s :=
  by 
    refine' ⟨fun hs t w hw₀ hw₁ hts => hs.sum_mem hw₀ hw₁ hts, _⟩
    intro h x y hx hy a b ha hb hab 
    byCases' h_cases : x = y
    ·
      rw [h_cases, ←add_smul, hab, one_smul]
      exact hy
    ·
      convert h {x, y} (fun z => if z = y then b else a) _ _ _
      ·
        simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl]
      ·
        simpIntro i hi 
        cases hi <;> subst i <;> simp [ha, hb, if_neg h_cases]
      ·
        simp only [sum_pair h_cases, if_neg h_cases, if_pos rfl, hab]
      ·
        simpIntro i hi 
        cases hi <;> subst i <;> simp [hx, hy, if_neg h_cases]

theorem Finset.center_mass_mem_convex_hull (t : Finset ι) {w : ι → R} (hw₀ : ∀ i (_ : i ∈ t), 0 ≤ w i)
  (hws : 0 < ∑i in t, w i) {z : ι → E} (hz : ∀ i (_ : i ∈ t), z i ∈ s) : t.center_mass w z ∈ convexHull R s :=
  (convex_convex_hull R s).center_mass_mem hw₀ hws fun i hi => subset_convex_hull R s$ hz i hi

/-- A refinement of `finset.center_mass_mem_convex_hull` when the indexed family is a `finset` of
the space. -/
theorem Finset.center_mass_id_mem_convex_hull (t : Finset E) {w : E → R} (hw₀ : ∀ i (_ : i ∈ t), 0 ≤ w i)
  (hws : 0 < ∑i in t, w i) : t.center_mass w id ∈ convexHull R (t : Set E) :=
  t.center_mass_mem_convex_hull hw₀ hws fun i => mem_coe.2

theorem affine_combination_eq_center_mass {ι : Type _} {t : Finset ι} {p : ι → E} {w : ι → R}
  (hw₂ : (∑i in t, w i) = 1) : affine_combination t p w = center_mass t w p :=
  by 
    rw [affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ w _ hw₂ (0 : E),
      Finset.weighted_vsub_of_point_apply, vadd_eq_add, add_zeroₓ, t.center_mass_eq_of_sum_1 _ hw₂]
    simpRw [vsub_eq_sub, sub_zero]

theorem affine_combination_mem_convex_hull {s : Finset ι} {v : ι → E} {w : ι → R} (hw₀ : ∀ i (_ : i ∈ s), 0 ≤ w i)
  (hw₁ : s.sum w = 1) : s.affine_combination v w ∈ convexHull R (range v) :=
  by 
    rw [affine_combination_eq_center_mass hw₁]
    apply s.center_mass_mem_convex_hull hw₀
    ·
      simp [hw₁]
    ·
      simp 

/-- The centroid can be regarded as a center of mass. -/
@[simp]
theorem Finset.centroid_eq_center_mass (s : Finset ι) (hs : s.nonempty) (p : ι → E) :
  s.centroid R p = s.center_mass (s.centroid_weights R) p :=
  affine_combination_eq_center_mass (s.sum_centroid_weights_eq_one_of_nonempty R hs)

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem finset.centroid_mem_convex_hull
(s : finset E)
(hs : s.nonempty) : «expr ∈ »(s.centroid R id, convex_hull R (s : set E)) :=
begin
  rw [expr s.centroid_eq_center_mass hs] [],
  apply [expr s.center_mass_id_mem_convex_hull],
  { simp [] [] ["only"] ["[", expr inv_nonneg, ",", expr implies_true_iff, ",", expr nat.cast_nonneg, ",", expr finset.centroid_weights_apply, "]"] [] [] },
  { have [ident hs_card] [":", expr «expr ≠ »((s.card : R), 0)] [],
    { simp [] [] [] ["[", expr finset.nonempty_iff_ne_empty.mp hs, "]"] [] [] },
    simp [] [] ["only"] ["[", expr hs_card, ",", expr finset.sum_const, ",", expr nsmul_eq_mul, ",", expr mul_inv_cancel, ",", expr ne.def, ",", expr not_false_iff, ",", expr finset.centroid_weights_apply, ",", expr zero_lt_one, "]"] [] [] }
end

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convex_hull_range_eq_exists_affine_combination
(v : ι → E) : «expr = »(convex_hull R (range v), {x | «expr∃ , »((s : finset ι)
  (w : ι → R)
  (hw₀ : ∀ i «expr ∈ » s, «expr ≤ »(0, w i))
  (hw₁ : «expr = »(s.sum w, 1)), «expr = »(s.affine_combination v w, x))}) :=
begin
  refine [expr subset.antisymm (convex_hull_min _ _) _],
  { intros [ident x, ident hx],
    obtain ["⟨", ident i, ",", ident hi, "⟩", ":=", expr set.mem_range.mp hx],
    refine [expr ⟨{i}, function.const ι (1 : R), by simp [] [] [] [] [] [], by simp [] [] [] [] [] [], by simp [] [] [] ["[", expr hi, "]"] [] []⟩] },
  { rw [expr convex] [],
    rintros [ident x, ident y, "⟨", ident s, ",", ident w, ",", ident hw₀, ",", ident hw₁, ",", ident rfl, "⟩", "⟨", ident s', ",", ident w', ",", ident hw₀', ",", ident hw₁', ",", ident rfl, "⟩", ident a, ident b, ident ha, ident hb, ident hab],
    let [ident W] [":", expr ι → R] [":=", expr λ
     i, «expr + »(if «expr ∈ »(i, s) then «expr * »(a, w i) else 0, if «expr ∈ »(i, s') then «expr * »(b, w' i) else 0)],
    have [ident hW₁] [":", expr «expr = »(«expr ∪ »(s, s').sum W, 1)] [],
    { rw ["[", expr sum_add_distrib, ",", "<-", expr sum_subset (subset_union_left s s'), ",", "<-", expr sum_subset (subset_union_right s s'), ",", expr sum_ite_of_true _ _ (λ
        i
        hi, hi), ",", expr sum_ite_of_true _ _ (λ
        i
        hi, hi), ",", "<-", expr mul_sum, ",", "<-", expr mul_sum, ",", expr hw₁, ",", expr hw₁', ",", "<-", expr add_mul, ",", expr hab, ",", expr mul_one, "]"] []; intros [ident i, ident hi, ident hi']; simp [] [] [] ["[", expr hi', "]"] [] [] },
    refine [expr ⟨«expr ∪ »(s, s'), W, _, hW₁, _⟩],
    { rintros [ident i, "-"],
      by_cases [expr hi, ":", expr «expr ∈ »(i, s)]; by_cases [expr hi', ":", expr «expr ∈ »(i, s')]; simp [] [] [] ["[", expr hi, ",", expr hi', ",", expr add_nonneg, ",", expr mul_nonneg ha (hw₀ i _), ",", expr mul_nonneg hb (hw₀' i _), "]"] [] [] },
    { simp_rw ["[", expr affine_combination_eq_linear_combination «expr ∪ »(s, s') v _ hW₁, ",", expr affine_combination_eq_linear_combination s v w hw₁, ",", expr affine_combination_eq_linear_combination s' v w' hw₁', ",", expr add_smul, ",", expr sum_add_distrib, "]"] [],
      rw ["[", "<-", expr sum_subset (subset_union_left s s'), ",", "<-", expr sum_subset (subset_union_right s s'), "]"] [],
      { simp [] [] ["only"] ["[", expr ite_smul, ",", expr sum_ite_of_true _ _ (λ
          i hi, hi), ",", expr mul_smul, ",", "<-", expr smul_sum, "]"] [] [] },
      { intros [ident i, ident hi, ident hi'],
        simp [] [] [] ["[", expr hi', "]"] [] [] },
      { intros [ident i, ident hi, ident hi'],
        simp [] [] [] ["[", expr hi', "]"] [] [] } } },
  { rintros [ident x, "⟨", ident s, ",", ident w, ",", ident hw₀, ",", ident hw₁, ",", ident rfl, "⟩"],
    exact [expr affine_combination_mem_convex_hull hw₀ hw₁] }
end

/-- Convex hull of `s` is equal to the set of all centers of masses of `finset`s `t`, `z '' t ⊆ s`.
This version allows finsets in any type in any universe. -/
theorem convex_hull_eq (s : Set E) :
  convexHull R s =
    { x:E |
      ∃ (ι : Type u')(t : Finset ι)(w : ι → R)(z : ι → E)(hw₀ : ∀ i (_ : i ∈ t), 0 ≤ w i)(hw₁ : (∑i in t, w i) = 1)(hz :
        ∀ i (_ : i ∈ t), z i ∈ s), t.center_mass w z = x } :=
  by 
    refine' subset.antisymm (convex_hull_min _ _) _
    ·
      intro x hx 
      use PUnit, {PUnit.unit}, fun _ => 1, fun _ => x, fun _ _ => zero_le_one, Finset.sum_singleton, fun _ _ => hx 
      simp only [Finset.centerMass, Finset.sum_singleton, inv_one, one_smul]
    ·
      rintro x y ⟨ι, sx, wx, zx, hwx₀, hwx₁, hzx, rfl⟩ ⟨ι', sy, wy, zy, hwy₀, hwy₁, hzy, rfl⟩ a b ha hb hab 
      rw [Finset.center_mass_segment' _ _ _ _ _ _ hwx₁ hwy₁ _ _ hab]
      refine' ⟨_, _, _, _, _, _, _, rfl⟩
      ·
        rintro i hi 
        rw [Finset.mem_union, Finset.mem_map, Finset.mem_map] at hi 
        rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;>
          simp only [Sum.elim_inl, Sum.elim_inr] <;> applyRules [mul_nonneg, hwx₀, hwy₀]
      ·
        simp [Finset.sum_sum_elim, finset.mul_sum.symm]
      ·
        intro i hi 
        rw [Finset.mem_union, Finset.mem_map, Finset.mem_map] at hi 
        rcases hi with (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩) <;> applyRules [hzx, hzy]
    ·
      rintro _ ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
      exact t.center_mass_mem_convex_hull hw₀ (hw₁.symm ▸ zero_lt_one) hz

theorem Finset.convex_hull_eq (s : Finset E) :
  convexHull R («expr↑ » s) =
    { x:E | ∃ (w : E → R)(hw₀ : ∀ y (_ : y ∈ s), 0 ≤ w y)(hw₁ : (∑y in s, w y) = 1), s.center_mass w id = x } :=
  by 
    refine' subset.antisymm (convex_hull_min _ _) _
    ·
      intro x hx 
      rw [Finset.mem_coe] at hx 
      refine' ⟨_, _, _, Finset.center_mass_ite_eq _ _ _ hx⟩
      ·
        intros 
        splitIfs 
        exacts[zero_le_one, le_reflₓ 0]
      ·
        rw [Finset.sum_ite_eq, if_pos hx]
    ·
      rintro x y ⟨wx, hwx₀, hwx₁, rfl⟩ ⟨wy, hwy₀, hwy₁, rfl⟩ a b ha hb hab 
      rw [Finset.center_mass_segment _ _ _ _ hwx₁ hwy₁ _ _ hab]
      refine' ⟨_, _, _, rfl⟩
      ·
        rintro i hi 
        applyRules [add_nonneg, mul_nonneg, hwx₀, hwy₀]
      ·
        simp only [Finset.sum_add_distrib, finset.mul_sum.symm, mul_oneₓ]
    ·
      rintro _ ⟨w, hw₀, hw₁, rfl⟩
      exact s.center_mass_mem_convex_hull (fun x hx => hw₀ _ hx) (hw₁.symm ▸ zero_lt_one) fun x hx => hx

theorem Set.Finite.convex_hull_eq {s : Set E} (hs : finite s) :
  convexHull R s =
    { x:E |
      ∃ (w : E → R)(hw₀ : ∀ y (_ : y ∈ s), 0 ≤ w y)(hw₁ : (∑y in hs.to_finset, w y) = 1),
        hs.to_finset.center_mass w id = x } :=
  by 
    simpa only [Set.Finite.coe_to_finset, Set.Finite.mem_to_finset, exists_prop] using hs.to_finset.convex_hull_eq

/-- A weak version of Carathéodory's theorem. -/
theorem convex_hull_eq_union_convex_hull_finite_subsets (s : Set E) :
  convexHull R s = ⋃(t : Finset E)(w : «expr↑ » t ⊆ s), convexHull R («expr↑ » t) :=
  by 
    refine' subset.antisymm _ _
    ·
      rw [convex_hull_eq]
      rintro x ⟨ι, t, w, z, hw₀, hw₁, hz, rfl⟩
      simp only [mem_Union]
      refine' ⟨t.image z, _, _⟩
      ·
        rw [coe_image, Set.image_subset_iff]
        exact hz
      ·
        apply t.center_mass_mem_convex_hull hw₀
        ·
          simp only [hw₁, zero_lt_one]
        ·
          exact fun i hi => Finset.mem_coe.2 (Finset.mem_image_of_mem _ hi)
    ·
      exact Union_subset fun i => Union_subset convex_hull_mono

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem convex_hull_prod
(s : set E)
(t : set F) : «expr = »(convex_hull R (s.prod t), (convex_hull R s).prod (convex_hull R t)) :=
begin
  refine [expr set.subset.antisymm _ _],
  { exact [expr convex_hull_min «expr $ »(set.prod_mono (subset_convex_hull _ _), subset_convex_hull _ _) «expr $ »((convex_convex_hull _ _).prod, convex_convex_hull _ _)] },
  rintro ["⟨", ident x, ",", ident y, "⟩", "⟨", ident hx, ",", ident hy, "⟩"],
  rw [expr convex_hull_eq] ["at", "⊢", ident hx, ident hy],
  obtain ["⟨", ident ι, ",", ident a, ",", ident w, ",", ident S, ",", ident hw, ",", ident hw', ",", ident hS, ",", ident hSp, "⟩", ":=", expr hx],
  obtain ["⟨", ident κ, ",", ident b, ",", ident v, ",", ident T, ",", ident hv, ",", ident hv', ",", ident hT, ",", ident hTp, "⟩", ":=", expr hy],
  have [ident h_sum] [":", expr «expr = »(«expr∑ in , »((i : «expr × »(ι, κ)), a.product b, «expr * »(w i.fst, v i.snd)), 1)] [],
  { rw ["[", expr finset.sum_product, ",", "<-", expr hw', "]"] [],
    congr,
    ext [] [ident i] [],
    have [] [":", expr «expr = »(«expr∑ in , »((y : κ), b, «expr * »(w i, v y)), «expr∑ in , »((y : κ), b, «expr * »(v y, w i)))] [],
    { congr,
      ext [] [] [],
      simp [] [] [] ["[", expr mul_comm, "]"] [] [] },
    rw ["[", expr this, ",", "<-", expr finset.sum_mul, ",", expr hv', "]"] [],
    simp [] [] [] [] [] [] },
  refine [expr ⟨«expr × »(ι, κ), a.product b, λ
    p, «expr * »(w p.1, v p.2), λ p, (S p.1, T p.2), λ p hp, _, h_sum, λ p hp, _, _⟩],
  { rw [expr mem_product] ["at", ident hp],
    exact [expr mul_nonneg (hw p.1 hp.1) (hv p.2 hp.2)] },
  { rw [expr mem_product] ["at", ident hp],
    exact [expr ⟨hS p.1 hp.1, hT p.2 hp.2⟩] },
  ext [] [] [],
  { rw ["[", "<-", expr hSp, ",", expr finset.center_mass_eq_of_sum_1 _ _ hw', ",", expr finset.center_mass_eq_of_sum_1 _ _ h_sum, "]"] [],
    simp_rw ["[", expr prod.fst_sum, ",", expr prod.smul_mk, "]"] [],
    rw [expr finset.sum_product] [],
    congr,
    ext [] [ident i] [],
    have [] [":", expr «expr = »(«expr∑ in , »((j : κ), b, «expr • »(«expr * »(w i, v j), S i)), «expr∑ in , »((j : κ), b, «expr • »(v j, «expr • »(w i, S i))))] [],
    { congr,
      ext [] [] [],
      rw ["[", expr mul_smul, ",", expr smul_comm, "]"] [] },
    rw ["[", expr this, ",", "<-", expr finset.sum_smul, ",", expr hv', ",", expr one_smul, "]"] [] },
  { rw ["[", "<-", expr hTp, ",", expr finset.center_mass_eq_of_sum_1 _ _ hv', ",", expr finset.center_mass_eq_of_sum_1 _ _ h_sum, "]"] [],
    simp_rw ["[", expr prod.snd_sum, ",", expr prod.smul_mk, "]"] [],
    rw ["[", expr finset.sum_product, ",", expr finset.sum_comm, "]"] [],
    congr,
    ext [] [ident j] [],
    simp_rw [expr mul_smul] [],
    rw ["[", "<-", expr finset.sum_smul, ",", expr hw', ",", expr one_smul, "]"] [] }
end

/-! ### `std_simplex` -/


variable(ι)[Fintype ι]{f : ι → R}

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
/-- `std_simplex 𝕜 ι` is the convex hull of the canonical basis in `ι → 𝕜`. -/
theorem convex_hull_basis_eq_std_simplex : «expr = »(convex_hull R «expr $ »(range, λ
  i j : ι, if «expr = »(i, j) then (1 : R) else 0), std_simplex R ι) :=
begin
  refine [expr subset.antisymm (convex_hull_min _ (convex_std_simplex R ι)) _],
  { rintros ["_", "⟨", ident i, ",", ident rfl, "⟩"],
    exact [expr ite_eq_mem_std_simplex R i] },
  { rintros [ident w, "⟨", ident hw₀, ",", ident hw₁, "⟩"],
    rw ["[", expr pi_eq_sum_univ w, ",", "<-", expr finset.univ.center_mass_eq_of_sum_1 _ hw₁, "]"] [],
    exact [expr finset.univ.center_mass_mem_convex_hull (λ
      i hi, hw₀ i) «expr ▸ »(hw₁.symm, zero_lt_one) (λ i hi, mem_range_self i)] }
end

variable{ι}

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The convex hull of a finite set is the image of the standard simplex in `s → ℝ`
under the linear map sending each function `w` to `∑ x in s, w x • x`.

Since we have no sums over finite sets, we use sum over `@finset.univ _ hs.fintype`.
The map is defined in terms of operations on `(s → ℝ) →ₗ[ℝ] ℝ` so that later we will not need
to prove that this map is linear. -/
theorem set.finite.convex_hull_eq_image
{s : set E}
(hs : finite s) : «expr = »(convex_hull R s, by haveI [] [] [":=", expr hs.fintype]; exact [expr «expr '' »(«expr⇑ »(«expr∑ , »((x : s), (@linear_map.proj R s _ (λ
       i, R) _ _ x).smul_right x.1)), std_simplex R s)]) :=
begin
  rw ["[", "<-", expr convex_hull_basis_eq_std_simplex, ",", "<-", expr linear_map.convex_hull_image, ",", "<-", expr set.range_comp, ",", expr («expr ∘ »), "]"] [],
  apply [expr congr_arg],
  convert [] [expr subtype.range_coe.symm] [],
  ext [] [ident x] [],
  simp [] [] [] ["[", expr linear_map.sum_apply, ",", expr ite_smul, ",", expr finset.filter_eq, "]"] [] []
end

/-- All values of a function `f ∈ std_simplex 𝕜 ι` belong to `[0, 1]`. -/
theorem mem_Icc_of_mem_std_simplex (hf : f ∈ StdSimplex R ι) x : f x ∈ Icc (0 : R) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y hy => hf.1 y) (Finset.mem_univ x)⟩

-- error in Analysis.Convex.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The convex hull of an affine basis is the intersection of the half-spaces defined by the
corresponding barycentric coordinates. -/
theorem convex_hull_affine_basis_eq_nonneg_barycentric
{ι : Type*}
(b : affine_basis ι R E) : «expr = »(convex_hull R (range b.points), {x | ∀ i, «expr ≤ »(0, b.coord i x)}) :=
begin
  rw [expr convex_hull_range_eq_exists_affine_combination] [],
  ext [] [ident x] [],
  split,
  { rintros ["⟨", ident s, ",", ident w, ",", ident hw₀, ",", ident hw₁, ",", ident rfl, "⟩", ident i],
    by_cases [expr hi, ":", expr «expr ∈ »(i, s)],
    { rw [expr b.coord_apply_combination_of_mem hi hw₁] [],
      exact [expr hw₀ i hi] },
    { rw [expr b.coord_apply_combination_of_not_mem hi hw₁] [] } },
  { intros [ident hx],
    have [ident hx'] [":", expr «expr ∈ »(x, affine_span R (range b.points))] [],
    { rw [expr b.tot] [],
      exact [expr affine_subspace.mem_top R E x] },
    obtain ["⟨", ident s, ",", ident w, ",", ident hw₁, ",", ident rfl, "⟩", ":=", expr (mem_affine_span_iff_eq_affine_combination R E).mp hx'],
    refine [expr ⟨s, w, _, hw₁, rfl⟩],
    intros [ident i, ident hi],
    specialize [expr hx i],
    rw [expr b.coord_apply_combination_of_mem hi hw₁] ["at", ident hx],
    exact [expr hx] }
end

