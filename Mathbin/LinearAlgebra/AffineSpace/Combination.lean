import Mathbin.Algebra.Invertible 
import Mathbin.Algebra.IndicatorFunction 
import Mathbin.LinearAlgebra.AffineSpace.AffineMap 
import Mathbin.LinearAlgebra.AffineSpace.AffineSubspace 
import Mathbin.LinearAlgebra.Finsupp 
import Mathbin.Tactic.FinCases

/-!
# Affine combinations of points

This file defines affine combinations of points.

## Main definitions

* `weighted_vsub_of_point` is a general weighted combination of
  subtractions with an explicit base point, yielding a vector.

* `weighted_vsub` uses an arbitrary choice of base point and is intended
  to be used when the sum of weights is 0, in which case the result is
  independent of the choice of base point.

* `affine_combination` adds the weighted combination to the arbitrary
  base point, yielding a point rather than a vector, and is intended
  to be used when the sum of weights is 1, in which case the result is
  independent of the choice of base point.

These definitions are for sums over a `finset`; versions for a
`fintype` may be obtained using `finset.univ`, while versions for a
`finsupp` may be obtained using `finsupp.support`.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/


noncomputable theory

open_locale BigOperators Classical Affine

namespace Finset

theorem univ_fin2 : (univ : Finset (Finₓ 2)) = {0, 1} :=
  by 
    ext x 
    finCases x <;> simp 

variable {k : Type _} {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V]

variable [S : affine_space V P]

include S

variable {ι : Type _} (s : Finset ι)

variable {ι₂ : Type _} (s₂ : Finset ι₂)

/-- A weighted sum of the results of subtracting a base point from the
given points, as a linear map on the weights.  The main cases of
interest are where the sum of the weights is 0, in which case the sum
is independent of the choice of base point, and where the sum of the
weights is 1, in which case the sum added to the base point is
independent of the choice of base point. -/
def weighted_vsub_of_point (p : ι → P) (b : P) : (ι → k) →ₗ[k] V :=
  ∑i in s, (LinearMap.proj i : (ι → k) →ₗ[k] k).smulRight (p i -ᵥ b)

@[simp]
theorem weighted_vsub_of_point_apply (w : ι → k) (p : ι → P) (b : P) :
  s.weighted_vsub_of_point p b w = ∑i in s, w i • (p i -ᵥ b) :=
  by 
    simp [weighted_vsub_of_point, LinearMap.sum_apply]

/-- Given a family of points, if we use a member of the family as a base point, the
`weighted_vsub_of_point` does not depend on the value of the weights at this point. -/
theorem weighted_vsub_of_point_eq_of_weights_eq (p : ι → P) (j : ι) (w₁ w₂ : ι → k) (hw : ∀ i, i ≠ j → w₁ i = w₂ i) :
  s.weighted_vsub_of_point p (p j) w₁ = s.weighted_vsub_of_point p (p j) w₂ :=
  by 
    simp only [Finset.weighted_vsub_of_point_apply]
    congr 
    ext i 
    cases' eq_or_ne i j with h h
    ·
      simp [h]
    ·
      simp [hw i h]

/-- The weighted sum is independent of the base point when the sum of
the weights is 0. -/
theorem weighted_vsub_of_point_eq_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : (∑i in s, w i) = 0) (b₁ b₂ : P) :
  s.weighted_vsub_of_point p b₁ w = s.weighted_vsub_of_point p b₂ w :=
  by 
    apply eq_of_sub_eq_zero 
    rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←sum_sub_distrib]
    convLHS => congr skip ext rw [←smul_sub, vsub_sub_vsub_cancel_left]
    rw [←sum_smul, h, zero_smul]

/-- The weighted sum, added to the base point, is independent of the
base point when the sum of the weights is 1. -/
theorem weighted_vsub_of_point_vadd_eq_of_sum_eq_one (w : ι → k) (p : ι → P) (h : (∑i in s, w i) = 1) (b₁ b₂ : P) :
  s.weighted_vsub_of_point p b₁ w +ᵥ b₁ = s.weighted_vsub_of_point p b₂ w +ᵥ b₂ :=
  by 
    erw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply, ←@vsub_eq_zero_iff_eq V, vadd_vsub_assoc,
      vsub_vadd_eq_vsub_sub, ←add_sub_assoc, add_commₓ, add_sub_assoc, ←sum_sub_distrib]
    convLHS => congr skip congr skip ext rw [←smul_sub, vsub_sub_vsub_cancel_left]
    rw [←sum_smul, h, one_smul, vsub_add_vsub_cancel, vsub_self]

/-- The weighted sum is unaffected by removing the base point, if
present, from the set of points. -/
@[simp]
theorem weighted_vsub_of_point_erase (w : ι → k) (p : ι → P) (i : ι) :
  (s.erase i).weightedVsubOfPoint p (p i) w = s.weighted_vsub_of_point p (p i) w :=
  by 
    rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply]
    apply sum_erase 
    rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by adding the base point, whether
or not present, to the set of points. -/
@[simp]
theorem weighted_vsub_of_point_insert [DecidableEq ι] (w : ι → k) (p : ι → P) (i : ι) :
  (insert i s).weightedVsubOfPoint p (p i) w = s.weighted_vsub_of_point p (p i) w :=
  by 
    rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply]
    apply sum_insert_zero 
    rw [vsub_self, smul_zero]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weighted_vsub_of_point_indicator_subset (w : ι → k) (p : ι → P) (b : P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub_of_point p b w = s₂.weighted_vsub_of_point p b (Set.indicator («expr↑ » s₁) w) :=
  by 
    rw [weighted_vsub_of_point_apply, weighted_vsub_of_point_apply]
    exact Set.sum_indicator_subset_of_eq_zero w (fun i wi => wi • (p i -ᵥ b : V)) h fun i => zero_smul k _

/-- A weighted sum, over the image of an embedding, equals a weighted
sum with the same points and weights over the original
`finset`. -/
theorem weighted_vsub_of_point_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) (b : P) :
  (s₂.map e).weightedVsubOfPoint p b w = s₂.weighted_vsub_of_point (p ∘ e) b (w ∘ e) :=
  by 
    simpRw [weighted_vsub_of_point_apply]
    exact Finset.sum_map _ _ _

/-- A weighted sum of the results of subtracting a default base point
from the given points, as a linear map on the weights.  This is
intended to be used when the sum of the weights is 0; that condition
is specified as a hypothesis on those lemmas that require it. -/
def weighted_vsub (p : ι → P) : (ι → k) →ₗ[k] V :=
  s.weighted_vsub_of_point p (Classical.choice S.nonempty)

/-- Applying `weighted_vsub` with given weights.  This is for the case
where a result involving a default base point is OK (for example, when
that base point will cancel out later); a more typical use case for
`weighted_vsub` would involve selecting a preferred base point with
`weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero` and then
using `weighted_vsub_of_point_apply`. -/
theorem weighted_vsub_apply (w : ι → k) (p : ι → P) :
  s.weighted_vsub p w = ∑i in s, w i • (p i -ᵥ Classical.choice S.nonempty) :=
  by 
    simp [weighted_vsub, LinearMap.sum_apply]

/-- `weighted_vsub` gives the sum of the results of subtracting any
base point, when the sum of the weights is 0. -/
theorem weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero (w : ι → k) (p : ι → P) (h : (∑i in s, w i) = 0)
  (b : P) : s.weighted_vsub p w = s.weighted_vsub_of_point p b w :=
  s.weighted_vsub_of_point_eq_of_sum_eq_zero w p h _ _

/-- The `weighted_vsub` for an empty set is 0. -/
@[simp]
theorem weighted_vsub_empty (w : ι → k) (p : ι → P) : (∅ : Finset ι).weightedVsub p w = (0 : V) :=
  by 
    simp [weighted_vsub_apply]

/-- The weighted sum is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem weighted_vsub_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
  s₁.weighted_vsub p w = s₂.weighted_vsub p (Set.indicator («expr↑ » s₁) w) :=
  weighted_vsub_of_point_indicator_subset _ _ _ h

/-- A weighted subtraction, over the image of an embedding, equals a
weighted subtraction with the same points and weights over the
original `finset`. -/
theorem weighted_vsub_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).weightedVsub p w = s₂.weighted_vsub (p ∘ e) (w ∘ e) :=
  s₂.weighted_vsub_of_point_map _ _ _ _

/-- A weighted sum of the results of subtracting a default base point
from the given points, added to that base point, as an affine map on
the weights.  This is intended to be used when the sum of the weights
is 1, in which case it is an affine combination (barycenter) of the
points with the given weights; that condition is specified as a
hypothesis on those lemmas that require it. -/
def affine_combination (p : ι → P) : (ι → k) →ᵃ[k] P :=
  { toFun := fun w => s.weighted_vsub_of_point p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty,
    linear := s.weighted_vsub p,
    map_vadd' :=
      fun w₁ w₂ =>
        by 
          simpRw [vadd_vadd, weighted_vsub, vadd_eq_add, LinearMap.map_add] }

/-- The linear map corresponding to `affine_combination` is
`weighted_vsub`. -/
@[simp]
theorem affine_combination_linear (p : ι → P) : (s.affine_combination p : (ι → k) →ᵃ[k] P).linear = s.weighted_vsub p :=
  rfl

/-- Applying `affine_combination` with given weights.  This is for the
case where a result involving a default base point is OK (for example,
when that base point will cancel out later); a more typical use case
for `affine_combination` would involve selecting a preferred base
point with
`affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one` and
then using `weighted_vsub_of_point_apply`. -/
theorem affine_combination_apply (w : ι → k) (p : ι → P) :
  s.affine_combination p w =
    s.weighted_vsub_of_point p (Classical.choice S.nonempty) w +ᵥ Classical.choice S.nonempty :=
  rfl

/-- `affine_combination` gives the sum with any base point, when the
sum of the weights is 1. -/
theorem affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one (w : ι → k) (p : ι → P) (h : (∑i in s, w i) = 1)
  (b : P) : s.affine_combination p w = s.weighted_vsub_of_point p b w +ᵥ b :=
  s.weighted_vsub_of_point_vadd_eq_of_sum_eq_one w p h _ _

/-- Adding a `weighted_vsub` to an `affine_combination`. -/
theorem weighted_vsub_vadd_affine_combination (w₁ w₂ : ι → k) (p : ι → P) :
  s.weighted_vsub p w₁ +ᵥ s.affine_combination p w₂ = s.affine_combination p (w₁+w₂) :=
  by 
    rw [←vadd_eq_add, AffineMap.map_vadd, affine_combination_linear]

/-- Subtracting two `affine_combination`s. -/
theorem affine_combination_vsub (w₁ w₂ : ι → k) (p : ι → P) :
  s.affine_combination p w₁ -ᵥ s.affine_combination p w₂ = s.weighted_vsub p (w₁ - w₂) :=
  by 
    rw [←AffineMap.linear_map_vsub, affine_combination_linear, vsub_eq_sub]

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem attach_affine_combination_of_injective
(s : finset P)
(w : P → k)
(f : s → P)
(hf : function.injective f) : «expr = »(s.attach.affine_combination f «expr ∘ »(w, f), (image f univ).affine_combination id w) :=
begin
  simp [] [] ["only"] ["[", expr affine_combination, ",", expr weighted_vsub_of_point_apply, ",", expr id.def, ",", expr vadd_right_cancel_iff, ",", expr function.comp_app, ",", expr affine_map.coe_mk, "]"] [] [],
  let [ident g₁] [":", expr s → V] [":=", expr λ i, «expr • »(w (f i), «expr -ᵥ »(f i, classical.choice S.nonempty))],
  let [ident g₂] [":", expr P → V] [":=", expr λ i, «expr • »(w i, «expr -ᵥ »(i, classical.choice S.nonempty))],
  change [expr «expr = »(univ.sum g₁, (image f univ).sum g₂)] [] [],
  have [ident hgf] [":", expr «expr = »(g₁, «expr ∘ »(g₂, f))] [],
  { ext [] [] [],
    simp [] [] [] [] [] [] },
  rw ["[", expr hgf, ",", expr sum_image, "]"] [],
  exact [expr λ _ _ _ _ hxy, hf hxy]
end

theorem attach_affine_combination_coe (s : Finset P) (w : P → k) :
  s.attach.affine_combination (coeₓ : s → P) (w ∘ coeₓ) = s.affine_combination id w :=
  by 
    rw [attach_affine_combination_of_injective s w (coeₓ : s → P) Subtype.coe_injective, univ_eq_attach,
      attach_image_coe]

omit S

/-- Viewing a module as an affine space modelled on itself, affine combinations are just linear
combinations. -/
@[simp]
theorem affine_combination_eq_linear_combination (s : Finset ι) (p : ι → V) (w : ι → k) (hw : (∑i in s, w i) = 1) :
  s.affine_combination p w = ∑i in s, w i • p i :=
  by 
    simp [s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w p hw 0]

include S

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An `affine_combination` equals a point if that point is in the set
and has weight 1 and the other points in the set have weight 0. -/
@[simp]
theorem affine_combination_of_eq_one_of_eq_zero
(w : ι → k)
(p : ι → P)
{i : ι}
(his : «expr ∈ »(i, s))
(hwi : «expr = »(w i, 1))
(hw0 : ∀ i2 «expr ∈ » s, «expr ≠ »(i2, i) → «expr = »(w i2, 0)) : «expr = »(s.affine_combination p w, p i) :=
begin
  have [ident h1] [":", expr «expr = »(«expr∑ in , »((i), s, w i), 1)] [":=", expr «expr ▸ »(hwi, sum_eq_single i hw0 (λ
     h, false.elim (h his)))],
  rw ["[", expr s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w p h1 (p i), ",", expr weighted_vsub_of_point_apply, "]"] [],
  convert [] [expr zero_vadd V (p i)] [],
  convert [] [expr sum_eq_zero _] [],
  intros [ident i2, ident hi2],
  by_cases [expr h, ":", expr «expr = »(i2, i)],
  { simp [] [] [] ["[", expr h, "]"] [] [] },
  { simp [] [] [] ["[", expr hw0 i2 hi2 h, "]"] [] [] }
end

/-- An affine combination is unaffected by changing the weights to the
corresponding indicator function and adding points to the set. -/
theorem affine_combination_indicator_subset (w : ι → k) (p : ι → P) {s₁ s₂ : Finset ι} (h : s₁ ⊆ s₂) :
  s₁.affine_combination p w = s₂.affine_combination p (Set.indicator («expr↑ » s₁) w) :=
  by 
    rw [affine_combination_apply, affine_combination_apply, weighted_vsub_of_point_indicator_subset _ _ _ h]

/-- An affine combination, over the image of an embedding, equals an
affine combination with the same points and weights over the original
`finset`. -/
theorem affine_combination_map (e : ι₂ ↪ ι) (w : ι → k) (p : ι → P) :
  (s₂.map e).affineCombination p w = s₂.affine_combination (p ∘ e) (w ∘ e) :=
  by 
    simpRw [affine_combination_apply, weighted_vsub_of_point_map]

variable {V}

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as
`weighted_vsub_of_point` using a `finset` lying within that subset and
with a given sum of weights if and only if it can be expressed as
`weighted_vsub_of_point` with that sum of weights for the
corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype {v : V} {x : k} {s : Set ι} {p : ι → P}
  {b : P} :
  (∃ (fs : Finset ι)(hfs : «expr↑ » fs ⊆ s)(w : ι → k)(hw : (∑i in fs, w i) = x), v = fs.weighted_vsub_of_point p b w) ↔
    ∃ (fs : Finset s)(w : s → k)(hw : (∑i in fs, w i) = x), v = fs.weighted_vsub_of_point (fun i : s => p i) b w :=
  by 
    simpRw [weighted_vsub_of_point_apply]
    split 
    ·
      rintro ⟨fs, hfs, w, rfl, rfl⟩
      use fs.subtype s, fun i => w i, sum_subtype_of_mem _ hfs, (sum_subtype_of_mem _ hfs).symm
    ·
      rintro ⟨fs, w, rfl, rfl⟩
      refine'
          ⟨fs.map (Function.Embedding.subtype _), map_subtype_subset _, fun i => if h : i ∈ s then w ⟨i, h⟩ else 0, _,
            _⟩ <;>
        simp 

variable (k)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A vector can be expressed as `weighted_vsub` using
a `finset` lying within that subset and with sum of weights 0 if and
only if it can be expressed as `weighted_vsub` with sum of weights 0
for the corresponding indexed family whose index type is the subtype
corresponding to that subset. -/
theorem eq_weighted_vsub_subset_iff_eq_weighted_vsub_subtype {v : V} {s : Set ι} {p : ι → P} :
  (∃ (fs : Finset ι)(hfs : «expr↑ » fs ⊆ s)(w : ι → k)(hw : (∑i in fs, w i) = 0), v = fs.weighted_vsub p w) ↔
    ∃ (fs : Finset s)(w : s → k)(hw : (∑i in fs, w i) = 0), v = fs.weighted_vsub (fun i : s => p i) w :=
  eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype

variable (V)

/-- Suppose an indexed family of points is given, along with a subset
of the index type.  A point can be expressed as an
`affine_combination` using a `finset` lying within that subset and
with sum of weights 1 if and only if it can be expressed an
`affine_combination` with sum of weights 1 for the corresponding
indexed family whose index type is the subtype corresponding to that
subset. -/
theorem eq_affine_combination_subset_iff_eq_affine_combination_subtype {p0 : P} {s : Set ι} {p : ι → P} :
  (∃ (fs : Finset ι)(hfs : «expr↑ » fs ⊆ s)(w : ι → k)(hw : (∑i in fs, w i) = 1), p0 = fs.affine_combination p w) ↔
    ∃ (fs : Finset s)(w : s → k)(hw : (∑i in fs, w i) = 1), p0 = fs.affine_combination (fun i : s => p i) w :=
  by 
    simpRw [affine_combination_apply, eq_vadd_iff_vsub_eq]
    exact eq_weighted_vsub_of_point_subset_iff_eq_weighted_vsub_of_point_subtype

variable {k V}

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Affine maps commute with affine combinations. -/
theorem map_affine_combination
{V₂ P₂ : Type*}
[add_comm_group V₂]
[module k V₂]
[expraffine_space() V₂ P₂]
(p : ι → P)
(w : ι → k)
(hw : «expr = »(s.sum w, 1))
(f : «expr →ᵃ[ ] »(P, k, P₂)) : «expr = »(f (s.affine_combination p w), s.affine_combination «expr ∘ »(f, p) w) :=
begin
  have [ident b] [] [":=", expr classical.choice (infer_instance : expraffine_space() V P).nonempty],
  have [ident b₂] [] [":=", expr classical.choice (infer_instance : expraffine_space() V₂ P₂).nonempty],
  rw ["[", expr s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w p hw b, ",", expr s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w «expr ∘ »(f, p) hw b₂, ",", "<-", expr s.weighted_vsub_of_point_vadd_eq_of_sum_eq_one w «expr ∘ »(f, p) hw (f b) b₂, "]"] [],
  simp [] [] ["only"] ["[", expr weighted_vsub_of_point_apply, ",", expr ring_hom.id_apply, ",", expr affine_map.map_vadd, ",", expr linear_map.map_smulₛₗ, ",", expr affine_map.linear_map_vsub, ",", expr linear_map.map_sum, "]"] [] []
end

end Finset

namespace Finset

variable (k : Type _) {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _} (s : Finset ι) {ι₂ : Type _} (s₂ : Finset ι₂)

/-- The weights for the centroid of some points. -/
def centroid_weights : ι → k :=
  Function.const ι ((card s : k)⁻¹)

/-- `centroid_weights` at any point. -/
@[simp]
theorem centroid_weights_apply (i : ι) : s.centroid_weights k i = (card s : k)⁻¹ :=
  rfl

/-- `centroid_weights` equals a constant function. -/
theorem centroid_weights_eq_const : s.centroid_weights k = Function.const ι ((card s : k)⁻¹) :=
  rfl

variable {k}

/-- The weights in the centroid sum to 1, if the number of points,
converted to `k`, is not zero. -/
theorem sum_centroid_weights_eq_one_of_cast_card_ne_zero (h : (card s : k) ≠ 0) :
  (∑i in s, s.centroid_weights k i) = 1 :=
  by 
    simp [h]

variable (k)

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is not zero. -/
theorem sum_centroid_weights_eq_one_of_card_ne_zero [CharZero k] (h : card s ≠ 0) :
  (∑i in s, s.centroid_weights k i) = 1 :=
  by 
    simp [h]

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the set is nonempty. -/
theorem sum_centroid_weights_eq_one_of_nonempty [CharZero k] (h : s.nonempty) : (∑i in s, s.centroid_weights k i) = 1 :=
  s.sum_centroid_weights_eq_one_of_card_ne_zero k (ne_of_gtₓ (card_pos.2 h))

/-- In the characteristic zero case, the weights in the centroid sum
to 1 if the number of points is `n + 1`. -/
theorem sum_centroid_weights_eq_one_of_card_eq_add_one [CharZero k] {n : ℕ} (h : card s = n+1) :
  (∑i in s, s.centroid_weights k i) = 1 :=
  s.sum_centroid_weights_eq_one_of_card_ne_zero k (h.symm ▸ Nat.succ_ne_zero n)

include V

/-- The centroid of some points.  Although defined for any `s`, this
is intended to be used in the case where the number of points,
converted to `k`, is not zero. -/
def centroid (p : ι → P) : P :=
  s.affine_combination p (s.centroid_weights k)

/-- The definition of the centroid. -/
theorem centroid_def (p : ι → P) : s.centroid k p = s.affine_combination p (s.centroid_weights k) :=
  rfl

theorem centroid_univ (s : Finset P) : univ.centroid k (coeₓ : s → P) = s.centroid k id :=
  by 
    rw [centroid, centroid, ←s.attach_affine_combination_coe]
    congr 
    ext 
    simp 

/-- The centroid of a single point. -/
@[simp]
theorem centroid_singleton (p : ι → P) (i : ι) : ({i} : Finset ι).centroid k p = p i :=
  by 
    simp [centroid_def, affine_combination_apply]

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The centroid of two points, expressed directly as adding a vector
to a point. -/
theorem centroid_insert_singleton
[invertible (2 : k)]
(p : ι → P)
(i₁
 i₂ : ι) : «expr = »(({i₁, i₂} : finset ι).centroid k p, «expr +ᵥ »(«expr • »((«expr ⁻¹»(2) : k), «expr -ᵥ »(p i₂, p i₁)), p i₁)) :=
begin
  by_cases [expr h, ":", expr «expr = »(i₁, i₂)],
  { simp [] [] [] ["[", expr h, "]"] [] [] },
  { have [ident hc] [":", expr «expr ≠ »((card ({i₁, i₂} : finset ι) : k), 0)] [],
    { rw ["[", expr card_insert_of_not_mem (not_mem_singleton.2 h), ",", expr card_singleton, "]"] [],
      norm_num [] [],
      exact [expr nonzero_of_invertible _] },
    rw ["[", expr centroid_def, ",", expr affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one _ _ _ (sum_centroid_weights_eq_one_of_cast_card_ne_zero _ hc) (p i₁), "]"] [],
    simp [] [] [] ["[", expr h, "]"] [] [],
    norm_num [] [] }
end

/-- The centroid of two points indexed by `fin 2`, expressed directly
as adding a vector to the first point. -/
theorem centroid_insert_singleton_fin [Invertible (2 : k)] (p : Finₓ 2 → P) :
  univ.centroid k p = (2⁻¹ : k) • (p 1 -ᵥ p 0) +ᵥ p 0 :=
  by 
    rw [univ_fin2]
    convert centroid_insert_singleton k p 0 1

/-- A centroid, over the image of an embedding, equals a centroid with
the same points and weights over the original `finset`. -/
theorem centroid_map (e : ι₂ ↪ ι) (p : ι → P) : (s₂.map e).centroid k p = s₂.centroid k (p ∘ e) :=
  by 
    simp [centroid_def, affine_combination_map, centroid_weights]

omit V

/-- `centroid_weights` gives the weights for the centroid as a
constant function, which is suitable when summing over the points
whose centroid is being taken.  This function gives the weights in a
form suitable for summing over a larger set of points, as an indicator
function that is zero outside the set whose centroid is being taken.
In the case of a `fintype`, the sum may be over `univ`. -/
def centroid_weights_indicator : ι → k :=
  Set.indicator («expr↑ » s) (s.centroid_weights k)

/-- The definition of `centroid_weights_indicator`. -/
theorem centroid_weights_indicator_def :
  s.centroid_weights_indicator k = Set.indicator («expr↑ » s) (s.centroid_weights k) :=
  rfl

/-- The sum of the weights for the centroid indexed by a `fintype`. -/
theorem sum_centroid_weights_indicator [Fintype ι] :
  (∑i, s.centroid_weights_indicator k i) = ∑i in s, s.centroid_weights k i :=
  (Set.sum_indicator_subset _ (subset_univ _)).symm

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is not
zero. -/
theorem sum_centroid_weights_indicator_eq_one_of_card_ne_zero [CharZero k] [Fintype ι] (h : card s ≠ 0) :
  (∑i, s.centroid_weights_indicator k i) = 1 :=
  by 
    rw [sum_centroid_weights_indicator]
    exact s.sum_centroid_weights_eq_one_of_card_ne_zero k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the set is nonempty. -/
theorem sum_centroid_weights_indicator_eq_one_of_nonempty [CharZero k] [Fintype ι] (h : s.nonempty) :
  (∑i, s.centroid_weights_indicator k i) = 1 :=
  by 
    rw [sum_centroid_weights_indicator]
    exact s.sum_centroid_weights_eq_one_of_nonempty k h

/-- In the characteristic zero case, the weights in the centroid
indexed by a `fintype` sum to 1 if the number of points is `n + 1`. -/
theorem sum_centroid_weights_indicator_eq_one_of_card_eq_add_one [CharZero k] [Fintype ι] {n : ℕ} (h : card s = n+1) :
  (∑i, s.centroid_weights_indicator k i) = 1 :=
  by 
    rw [sum_centroid_weights_indicator]
    exact s.sum_centroid_weights_eq_one_of_card_eq_add_one k h

include V

/-- The centroid as an affine combination over a `fintype`. -/
theorem centroid_eq_affine_combination_fintype [Fintype ι] (p : ι → P) :
  s.centroid k p = univ.affineCombination p (s.centroid_weights_indicator k) :=
  affine_combination_indicator_subset _ _ (subset_univ _)

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An indexed family of points that is injective on the given
`finset` has the same centroid as the image of that `finset`.  This is
stated in terms of a set equal to the image to provide control of
definitional equality for the index type used for the centroid of the
image. -/
theorem centroid_eq_centroid_image_of_inj_on
{p : ι → P}
(hi : ∀ i j «expr ∈ » s, «expr = »(p i, p j) → «expr = »(i, j))
{ps : set P}
[fintype ps]
(hps : «expr = »(ps, «expr '' »(p, «expr↑ »(s)))) : «expr = »(s.centroid k p, (univ : finset ps).centroid k (λ x, x)) :=
begin
  let [ident f] [":", expr «expr '' »(p, «expr↑ »(s)) → ι] [":=", expr λ x, x.property.some],
  have [ident hf] [":", expr ∀
   x, «expr ∧ »(«expr ∈ »(f x, s), «expr = »(p (f x), x))] [":=", expr λ x, x.property.some_spec],
  let [ident f'] [":", expr ps → ι] [":=", expr λ x, f ⟨x, «expr ▸ »(hps, x.property)⟩],
  have [ident hf'] [":", expr ∀
   x, «expr ∧ »(«expr ∈ »(f' x, s), «expr = »(p (f' x), x))] [":=", expr λ x, hf ⟨x, «expr ▸ »(hps, x.property)⟩],
  have [ident hf'i] [":", expr function.injective f'] [],
  { intros [ident x, ident y, ident h],
    rw ["[", expr subtype.ext_iff, ",", "<-", expr (hf' x).2, ",", "<-", expr (hf' y).2, ",", expr h, "]"] [] },
  let [ident f'e] [":", expr «expr ↪ »(ps, ι)] [":=", expr ⟨f', hf'i⟩],
  have [ident hu] [":", expr «expr = »(finset.univ.map f'e, s)] [],
  { ext [] [ident x] [],
    rw [expr mem_map] [],
    split,
    { rintros ["⟨", ident i, ",", "_", ",", ident rfl, "⟩"],
      exact [expr (hf' i).1] },
    { intro [ident hx],
      use ["[", expr ⟨p x, «expr ▸ »(hps.symm, set.mem_image_of_mem _ hx)⟩, ",", expr mem_univ _, "]"],
      refine [expr hi _ _ (hf' _).1 hx _],
      rw [expr (hf' _).2] [],
      refl } },
  rw ["[", "<-", expr hu, ",", expr centroid_map, "]"] [],
  congr' [] ["with", ident x],
  change [expr «expr = »(p (f' x), «expr↑ »(x))] [] [],
  rw [expr (hf' x).2] []
end

/-- Two indexed families of points that are injective on the given
`finset`s and with the same points in the image of those `finset`s
have the same centroid. -/
theorem centroid_eq_of_inj_on_of_image_eq {p : ι → P} (hi : ∀ i j _ : i ∈ s _ : j ∈ s, p i = p j → i = j) {p₂ : ι₂ → P}
  (hi₂ : ∀ i j _ : i ∈ s₂ _ : j ∈ s₂, p₂ i = p₂ j → i = j) (he : p '' «expr↑ » s = p₂ '' «expr↑ » s₂) :
  s.centroid k p = s₂.centroid k p₂ :=
  by 
    rw [s.centroid_eq_centroid_image_of_inj_on k hi rfl, s₂.centroid_eq_centroid_image_of_inj_on k hi₂ he]

end Finset

section AffineSpace'

variable {k : Type _} {V : Type _} {P : Type _} [Ringₓ k] [AddCommGroupₓ V] [Module k V] [affine_space V P]

variable {ι : Type _}

include V

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A `weighted_vsub` with sum of weights 0 is in the `vector_span` of
an indexed family. -/
theorem weighted_vsub_mem_vector_span
{s : finset ι}
{w : ι → k}
(h : «expr = »(«expr∑ in , »((i), s, w i), 0))
(p : ι → P) : «expr ∈ »(s.weighted_vsub p w, vector_span k (set.range p)) :=
begin
  rcases [expr is_empty_or_nonempty ι, "with", ident hι, "|", "⟨", "⟨", ident i0, "⟩", "⟩"],
  { resetI,
    simp [] [] [] ["[", expr finset.eq_empty_of_is_empty s, "]"] [] [] },
  { rw ["[", expr vector_span_range_eq_span_range_vsub_right k p i0, ",", "<-", expr set.image_univ, ",", expr finsupp.mem_span_image_iff_total, ",", expr finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero s w p h (p i0), ",", expr finset.weighted_vsub_of_point_apply, "]"] [],
    let [ident w'] [] [":=", expr set.indicator «expr↑ »(s) w],
    have [ident hwx] [":", expr ∀
     i, «expr ≠ »(w' i, 0) → «expr ∈ »(i, s)] [":=", expr λ i, set.mem_of_indicator_ne_zero],
    use ["[", expr finsupp.on_finset s w' hwx, ",", expr set.subset_univ _, "]"],
    rw ["[", expr finsupp.total_apply, ",", expr finsupp.on_finset_sum hwx, "]"] [],
    { apply [expr finset.sum_congr rfl],
      intros [ident i, ident hi],
      simp [] [] [] ["[", expr w', ",", expr set.indicator_apply, ",", expr if_pos hi, "]"] [] [] },
    { exact [expr λ _, zero_smul k _] } }
end

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An `affine_combination` with sum of weights 1 is in the
`affine_span` of an indexed family, if the underlying ring is
nontrivial. -/
theorem affine_combination_mem_affine_span
[nontrivial k]
{s : finset ι}
{w : ι → k}
(h : «expr = »(«expr∑ in , »((i), s, w i), 1))
(p : ι → P) : «expr ∈ »(s.affine_combination p w, affine_span k (set.range p)) :=
begin
  have [ident hnz] [":", expr «expr ≠ »(«expr∑ in , »((i), s, w i), 0)] [":=", expr «expr ▸ »(h.symm, one_ne_zero)],
  have [ident hn] [":", expr s.nonempty] [":=", expr finset.nonempty_of_sum_ne_zero hnz],
  cases [expr hn] ["with", ident i1, ident hi1],
  let [ident w1] [":", expr ι → k] [":=", expr function.update (function.const ι 0) i1 1],
  have [ident hw1] [":", expr «expr = »(«expr∑ in , »((i), s, w1 i), 1)] [],
  { rw ["[", expr finset.sum_update_of_mem hi1, ",", expr finset.sum_const_zero, ",", expr add_zero, "]"] [] },
  have [ident hw1s] [":", expr «expr = »(s.affine_combination p w1, p i1)] [":=", expr s.affine_combination_of_eq_one_of_eq_zero w1 p hi1 (function.update_same _ _ _) (λ
    _ _ hne, function.update_noteq hne _ _)],
  have [ident hv] [":", expr «expr ∈ »(«expr -ᵥ »(s.affine_combination p w, p i1), (affine_span k (set.range p)).direction)] [],
  { rw ["[", expr direction_affine_span, ",", "<-", expr hw1s, ",", expr finset.affine_combination_vsub, "]"] [],
    apply [expr weighted_vsub_mem_vector_span],
    simp [] [] [] ["[", expr pi.sub_apply, ",", expr h, ",", expr hw1, "]"] [] [] },
  rw ["<-", expr vsub_vadd (s.affine_combination p w) (p i1)] [],
  exact [expr affine_subspace.vadd_mem_of_mem_direction hv (mem_affine_span k (set.mem_range_self _))]
end

variable (k) {V}

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A vector is in the `vector_span` of an indexed family if and only
if it is a `weighted_vsub` with sum of weights 0. -/
theorem mem_vector_span_iff_eq_weighted_vsub
{v : V}
{p : ι → P} : «expr ↔ »(«expr ∈ »(v, vector_span k (set.range p)), «expr∃ , »((s : finset ι)
  (w : ι → k)
  (h : «expr = »(«expr∑ in , »((i), s, w i), 0)), «expr = »(v, s.weighted_vsub p w))) :=
begin
  split,
  { rcases [expr is_empty_or_nonempty ι, "with", ident hι, "|", "⟨", "⟨", ident i0, "⟩", "⟩"],
    swap,
    { rw ["[", expr vector_span_range_eq_span_range_vsub_right k p i0, ",", "<-", expr set.image_univ, ",", expr finsupp.mem_span_image_iff_total, "]"] [],
      rintros ["⟨", ident l, ",", ident hl, ",", ident hv, "⟩"],
      use [expr insert i0 l.support],
      set [] [ident w] [] [":="] [expr «expr - »((l : ι → k), function.update (function.const ι 0 : ι → k) i0 «expr∑ in , »((i), l.support, l i))] ["with", ident hwdef],
      use [expr w],
      have [ident hw] [":", expr «expr = »(«expr∑ in , »((i), insert i0 l.support, w i), 0)] [],
      { rw [expr hwdef] [],
        simp_rw ["[", expr pi.sub_apply, ",", expr finset.sum_sub_distrib, ",", expr finset.sum_update_of_mem (finset.mem_insert_self _ _), ",", expr finset.sum_const_zero, ",", expr finset.sum_insert_of_eq_zero_if_not_mem finsupp.not_mem_support_iff.1, ",", expr add_zero, ",", expr sub_self, "]"] [] },
      use [expr hw],
      have [ident hz] [":", expr «expr = »(«expr • »(w i0, («expr -ᵥ »(p i0, p i0) : V)), 0)] [":=", expr «expr ▸ »((vsub_self (p i0)).symm, smul_zero _)],
      change [expr «expr = »(λ i, «expr • »(w i, («expr -ᵥ »(p i, p i0) : V)) i0, 0)] [] ["at", ident hz],
      rw ["[", expr finset.weighted_vsub_eq_weighted_vsub_of_point_of_sum_eq_zero _ w p hw (p i0), ",", expr finset.weighted_vsub_of_point_apply, ",", "<-", expr hv, ",", expr finsupp.total_apply, ",", expr finset.sum_insert_zero hz, "]"] [],
      change [expr «expr = »(«expr∑ in , »((i), l.support, «expr • »(l i, _)), _)] [] [],
      congr' [] ["with", ident i],
      by_cases [expr h, ":", expr «expr = »(i, i0)],
      { simp [] [] [] ["[", expr h, "]"] [] [] },
      { simp [] [] [] ["[", expr hwdef, ",", expr h, "]"] [] [] } },
    { resetI,
      rw ["[", expr set.range_eq_empty, ",", expr vector_span_empty, ",", expr submodule.mem_bot, "]"] [],
      rintro [ident rfl],
      use ["[", expr «expr∅»(), "]"],
      simp [] [] [] [] [] [] } },
  { rintros ["⟨", ident s, ",", ident w, ",", ident hw, ",", ident rfl, "⟩"],
    exact [expr weighted_vsub_mem_vector_span hw p] }
end

variable {k}

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A point in the `affine_span` of an indexed family is an
`affine_combination` with sum of weights 1. See also
`eq_affine_combination_of_mem_affine_span_of_fintype`. -/
theorem eq_affine_combination_of_mem_affine_span
{p1 : P}
{p : ι → P}
(h : «expr ∈ »(p1, affine_span k (set.range p))) : «expr∃ , »((s : finset ι)
 (w : ι → k)
 (hw : «expr = »(«expr∑ in , »((i), s, w i), 1)), «expr = »(p1, s.affine_combination p w)) :=
begin
  have [ident hn] [":", expr (affine_span k (set.range p) : set P).nonempty] [":=", expr ⟨p1, h⟩],
  rw ["[", expr affine_span_nonempty, ",", expr set.range_nonempty_iff_nonempty, "]"] ["at", ident hn],
  cases [expr hn] ["with", ident i0],
  have [ident h0] [":", expr «expr ∈ »(p i0, affine_span k (set.range p))] [":=", expr mem_affine_span k (set.mem_range_self i0)],
  have [ident hd] [":", expr «expr ∈ »(«expr -ᵥ »(p1, p i0), (affine_span k (set.range p)).direction)] [":=", expr affine_subspace.vsub_mem_direction h h0],
  rw ["[", expr direction_affine_span, ",", expr mem_vector_span_iff_eq_weighted_vsub, "]"] ["at", ident hd],
  rcases [expr hd, "with", "⟨", ident s, ",", ident w, ",", ident h, ",", ident hs, "⟩"],
  let [ident s'] [] [":=", expr insert i0 s],
  let [ident w'] [] [":=", expr set.indicator «expr↑ »(s) w],
  have [ident h'] [":", expr «expr = »(«expr∑ in , »((i), s', w' i), 0)] [],
  { rw ["[", "<-", expr h, ",", expr set.sum_indicator_subset _ (finset.subset_insert i0 s), "]"] [] },
  have [ident hs'] [":", expr «expr = »(s'.weighted_vsub p w', «expr -ᵥ »(p1, p i0))] [],
  { rw [expr hs] [],
    exact [expr (finset.weighted_vsub_indicator_subset _ _ (finset.subset_insert i0 s)).symm] },
  let [ident w0] [":", expr ι → k] [":=", expr function.update (function.const ι 0) i0 1],
  have [ident hw0] [":", expr «expr = »(«expr∑ in , »((i), s', w0 i), 1)] [],
  { rw ["[", expr finset.sum_update_of_mem (finset.mem_insert_self _ _), ",", expr finset.sum_const_zero, ",", expr add_zero, "]"] [] },
  have [ident hw0s] [":", expr «expr = »(s'.affine_combination p w0, p i0)] [":=", expr s'.affine_combination_of_eq_one_of_eq_zero w0 p (finset.mem_insert_self _ _) (function.update_same _ _ _) (λ
    _ _ hne, function.update_noteq hne _ _)],
  use ["[", expr s', ",", expr «expr + »(w0, w'), "]"],
  split,
  { simp [] [] [] ["[", expr pi.add_apply, ",", expr finset.sum_add_distrib, ",", expr hw0, ",", expr h', "]"] [] [] },
  { rw ["[", expr add_comm, ",", "<-", expr finset.weighted_vsub_vadd_affine_combination, ",", expr hw0s, ",", expr hs', ",", expr vsub_vadd, "]"] [] }
end

theorem eq_affine_combination_of_mem_affine_span_of_fintype [Fintype ι] {p1 : P} {p : ι → P}
  (h : p1 ∈ affineSpan k (Set.Range p)) : ∃ (w : ι → k)(hw : (∑i, w i) = 1), p1 = Finset.univ.affineCombination p w :=
  by 
    obtain ⟨s, w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span h 
    refine' ⟨(s : Set ι).indicator w, _, Finset.affine_combination_indicator_subset w p s.subset_univ⟩
    simp only [Finset.mem_coe, Set.indicator_apply, ←hw]
    convert Fintype.sum_extend_by_zero s w 
    ext i 
    congr

variable (k V)

/-- A point is in the `affine_span` of an indexed family if and only
if it is an `affine_combination` with sum of weights 1, provided the
underlying ring is nontrivial. -/
theorem mem_affine_span_iff_eq_affine_combination [Nontrivial k] {p1 : P} {p : ι → P} :
  p1 ∈ affineSpan k (Set.Range p) ↔
    ∃ (s : Finset ι)(w : ι → k)(hw : (∑i in s, w i) = 1), p1 = s.affine_combination p w :=
  by 
    split 
    ·
      exact eq_affine_combination_of_mem_affine_span
    ·
      rintro ⟨s, w, hw, rfl⟩
      exact affine_combination_mem_affine_span hw p

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a family of points together with a chosen base point in that family, membership of the
affine span of this family corresponds to an identity in terms of `weighted_vsub_of_point`, with
weights that are not required to sum to 1. -/
theorem mem_affine_span_iff_eq_weighted_vsub_of_point_vadd
[nontrivial k]
(p : ι → P)
(j : ι)
(q : P) : «expr ↔ »(«expr ∈ »(q, affine_span k (set.range p)), «expr∃ , »((s : finset ι)
  (w : ι → k), «expr = »(q, «expr +ᵥ »(s.weighted_vsub_of_point p (p j) w, p j)))) :=
begin
  split,
  { intros [ident hq],
    obtain ["⟨", ident s, ",", ident w, ",", ident hw, ",", ident rfl, "⟩", ":=", expr eq_affine_combination_of_mem_affine_span hq],
    exact [expr ⟨s, w, s.affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w p hw (p j)⟩] },
  { rintros ["⟨", ident s, ",", ident w, ",", ident rfl, "⟩"],
    classical,
    let [ident w'] [":", expr ι → k] [":=", expr function.update w j «expr - »(1, «expr \ »(s, {j}).sum w)],
    have [ident h₁] [":", expr «expr = »((insert j s).sum w', 1)] [],
    { by_cases [expr hj, ":", expr «expr ∈ »(j, s)],
      { simp [] [] [] ["[", expr finset.sum_update_of_mem hj, ",", expr finset.insert_eq_of_mem hj, "]"] [] [] },
      { simp [] [] [] ["[", expr w', ",", expr finset.sum_insert hj, ",", expr finset.sum_update_of_not_mem hj, ",", expr hj, "]"] [] [] } },
    have [ident hww] [":", expr ∀ i, «expr ≠ »(i, j) → «expr = »(w i, w' i)] [],
    { intros [ident i, ident hij],
      simp [] [] [] ["[", expr w', ",", expr hij, "]"] [] [] },
    rw ["[", expr s.weighted_vsub_of_point_eq_of_weights_eq p j w w' hww, ",", "<-", expr s.weighted_vsub_of_point_insert w' p j, ",", "<-", expr (insert j s).affine_combination_eq_weighted_vsub_of_point_vadd_of_sum_eq_one w' p h₁ (p j), "]"] [],
    exact [expr affine_combination_mem_affine_span h₁ p] }
end

variable {k V}

-- error in LinearAlgebra.AffineSpace.Combination: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a set of points, together with a chosen base point in this set, if we affinely transport
all other members of the set along the line joining them to this base point, the affine span is
unchanged. -/
theorem affine_span_eq_affine_span_line_map_units
[nontrivial k]
{s : set P}
{p : P}
(hp : «expr ∈ »(p, s))
(w : s → units k) : «expr = »(affine_span k (set.range (λ
   q : s, affine_map.line_map p «expr↑ »(q) (w q : k))), affine_span k s) :=
begin
  have [] [":", expr «expr = »(s, set.range (coe : s → P))] [],
  { simp [] [] [] [] [] [] },
  conv_rhs [] [] { rw [expr this] },
  apply [expr le_antisymm]; intros [ident q, ident hq]; erw [expr mem_affine_span_iff_eq_weighted_vsub_of_point_vadd k V _ (⟨p, hp⟩ : s) q] ["at", ident hq, "⊢"]; obtain ["⟨", ident t, ",", ident μ, ",", ident rfl, "⟩", ":=", expr hq]; use [expr t]; [use [expr λ
    x, «expr * »(μ x, «expr↑ »(w x))], use [expr λ
    x, «expr * »(μ x, «expr↑ »(«expr ⁻¹»(w x)))]]; simp [] [] [] ["[", expr smul_smul, "]"] [] []
end

end AffineSpace'

section DivisionRing

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _}

include V

open Set Finset

/-- The centroid lies in the affine span if the number of points,
converted to `k`, is not zero. -/
theorem centroid_mem_affine_span_of_cast_card_ne_zero {s : Finset ι} (p : ι → P) (h : (card s : k) ≠ 0) :
  s.centroid k p ∈ affineSpan k (range p) :=
  affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_cast_card_ne_zero h) p

variable (k)

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is not zero. -/
theorem centroid_mem_affine_span_of_card_ne_zero [CharZero k] {s : Finset ι} (p : ι → P) (h : card s ≠ 0) :
  s.centroid k p ∈ affineSpan k (range p) :=
  affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_card_ne_zero k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the set is nonempty. -/
theorem centroid_mem_affine_span_of_nonempty [CharZero k] {s : Finset ι} (p : ι → P) (h : s.nonempty) :
  s.centroid k p ∈ affineSpan k (range p) :=
  affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_nonempty k h) p

/-- In the characteristic zero case, the centroid lies in the affine
span if the number of points is `n + 1`. -/
theorem centroid_mem_affine_span_of_card_eq_add_one [CharZero k] {s : Finset ι} (p : ι → P) {n : ℕ} (h : card s = n+1) :
  s.centroid k p ∈ affineSpan k (range p) :=
  affine_combination_mem_affine_span (s.sum_centroid_weights_eq_one_of_card_eq_add_one k h) p

end DivisionRing

namespace AffineMap

variable {k : Type _} {V : Type _} (P : Type _) [CommRingₓ k] [AddCommGroupₓ V] [Module k V]

variable [affine_space V P] {ι : Type _} (s : Finset ι)

include V

/-- A weighted sum, as an affine map on the points involved. -/
def weighted_vsub_of_point (w : ι → k) : (ι → P) × P →ᵃ[k] V :=
  { toFun := fun p => s.weighted_vsub_of_point p.fst p.snd w,
    linear := ∑i in s, w i • ((LinearMap.proj i).comp (LinearMap.fst _ _ _) - LinearMap.snd _ _ _),
    map_vadd' :=
      by 
        rintro ⟨p, b⟩ ⟨v, b'⟩
        simp [LinearMap.sum_apply, Finset.weightedVsubOfPoint, vsub_vadd_eq_vsub_sub, vadd_vsub_assoc, add_sub,
          ←sub_add_eq_add_sub, smul_add, Finset.sum_add_distrib] }

end AffineMap

