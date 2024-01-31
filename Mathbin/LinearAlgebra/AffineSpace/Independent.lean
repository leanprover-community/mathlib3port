/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Data.Finset.Sort
import Data.Fin.VecNotation
import Data.Sign
import LinearAlgebra.AffineSpace.Combination
import LinearAlgebra.AffineSpace.AffineEquiv
import LinearAlgebra.Basis

#align_import linear_algebra.affine_space.independent from "leanprover-community/mathlib"@"4f81bc21e32048db7344b7867946e992cf5f68cc"

/-!
# Affine independence

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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


noncomputable section

open scoped BigOperators Affine

open Function

section AffineIndependent

variable (k : Type _) {V : Type _} {P : Type _} [Ring k] [AddCommGroup V] [Module k V]

variable [affine_space V P] {ι : Type _}

#print AffineIndependent /-
/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k), ∑ i in s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0
#align affine_independent AffineIndependent
-/

#print affineIndependent_def /-
/-- The definition of `affine_independent`. -/
theorem affineIndependent_def (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k),
        ∑ i in s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0 :=
  Iff.rfl
#align affine_independent_def affineIndependent_def
-/

#print affineIndependent_of_subsingleton /-
/-- A family with at most one point is affinely independent. -/
theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p :=
  fun s w h hs i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi
#align affine_independent_of_subsingleton affineIndependent_of_subsingleton
-/

#print affineIndependent_iff_of_fintype /-
/-- A family indexed by a `fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `finset.univ` (where
the sum of the weights is 0) are 0. -/
theorem affineIndependent_iff_of_fintype [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w : ι → k, ∑ i, w i = 0 → Finset.univ.weightedVSub p w = (0 : V) → ∀ i, w i = 0 :=
  by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs 
    rw [Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw 
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [hi] using h
#align affine_independent_iff_of_fintype affineIndependent_iff_of_fintype
-/

#print affineIndependent_iff_linearIndependent_vsub /-
/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
theorem affineIndependent_iff_linearIndependent_vsub (p : ι → P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  classical
#align affine_independent_iff_linear_independent_vsub affineIndependent_iff_linearIndependent_vsub
-/

#print affineIndependent_set_iff_linearIndependent_vsub /-
/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
theorem affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
    AffineIndependent k (fun p => p : s → P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) :=
  by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s → P) ⟨p₁, hp₁⟩]
  constructor
  · intro h
    have hv : ∀ v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → { x : s // x ≠ ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_diff (hv x)⟩, fun hx =>
        Set.not_mem_of_mem_diff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert
      h.comp f fun x1 x2 hx =>
        Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
  · intro h
    let f : { x : s // x ≠ ⟨p₁, hp₁⟩ } → (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert
      h.comp f fun x1 x2 hx => Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))
#align affine_independent_set_iff_linear_independent_vsub affineIndependent_set_iff_linearIndependent_vsub
-/

#print linearIndependent_set_iff_affineIndependent_vadd_union_singleton /-
/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set V}
    (hs : ∀ v ∈ s, v ≠ (0 : V)) (p₁ : P) :
    LinearIndependent k (fun v => v : s → V) ↔
      AffineIndependent k (fun p => p : {p₁} ∪ (fun v => v +ᵥ p₁) '' s → P) :=
  by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} ∪ (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s :=
    by
    simp_rw [Set.union_diff_left, Set.image_diff (vsub_left_injective p₁), Set.image_image,
      Set.image_singleton, vsub_self, vadd_vsub, Set.image_id']
    exact Set.diff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]
#align linear_independent_set_iff_affine_independent_vadd_union_singleton linearIndependent_set_iff_affineIndependent_vadd_union_singleton
-/

#print affineIndependent_iff_indicator_eq_of_affineCombination_eq /-
/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `set.indicator`. -/
theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s1 s2 : Finset ι) (w1 w2 : ι → k),
        ∑ i in s1, w1 i = 1 →
          ∑ i in s2, w2 i = 1 →
            s1.affineCombination k p w1 = s2.affineCombination k p w2 →
              Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2 :=
  by classical
#align affine_independent_iff_indicator_eq_of_affine_combination_eq affineIndependent_iff_indicator_eq_of_affineCombination_eq
-/

#print affineIndependent_iff_eq_of_fintype_affineCombination_eq /-
/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w1 w2 : ι → k,
        ∑ i, w1 i = 1 →
          ∑ i, w2 i = 1 →
            Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination k p w2 → w1 = w2 :=
  by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : ∑ i, (s1 : Set ι).indicator w1 i = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s1)] at hw1 
    have hw2' : ∑ i, (s2 : Set ι).indicator w2 i = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s2)] at hw2 
    rw [Finset.affineCombination_indicator_subset w1 p (Finset.subset_univ s1),
      Finset.affineCombination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq 
    exact h _ _ hw1' hw2' hweq
#align affine_independent_iff_eq_of_fintype_affine_combination_eq affineIndependent_iff_eq_of_fintype_affineCombination_eq
-/

variable {k}

#print AffineIndependent.units_lineMap /-
/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `linear_independent.units_smul`. -/
theorem AffineIndependent.units_lineMap {p : ι → P} (hp : AffineIndependent k p) (j : ι)
    (w : ι → Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) :=
  by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same]
  exact hp.units_smul fun i => w i
#align affine_independent.units_line_map AffineIndependent.units_lineMap
-/

#print AffineIndependent.indicator_eq_of_affineCombination_eq /-
theorem AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i in s₁, w₁ i = 1)
    (hw₂ : ∑ i in s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineCombination k p w₂) :
    Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂ :=
  (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h
#align affine_independent.indicator_eq_of_affine_combination_eq AffineIndependent.indicator_eq_of_affineCombination_eq
-/

#print AffineIndependent.injective /-
/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Function.Injective p :=
  by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha 
  by_contra hij'
  exact ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr hij)
#align affine_independent.injective AffineIndependent.injective
-/

#print AffineIndependent.comp_embedding /-
/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
theorem AffineIndependent.comp_embedding {ι2 : Type _} (f : ι2 ↪ ι) {p : ι → P}
    (ha : AffineIndependent k p) : AffineIndependent k (p ∘ f) := by classical
#align affine_independent.comp_embedding AffineIndependent.comp_embedding
-/

#print AffineIndependent.subtype /-
/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
protected theorem AffineIndependent.subtype {p : ι → P} (ha : AffineIndependent k p) (s : Set ι) :
    AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (Embedding.subtype _)
#align affine_independent.subtype AffineIndependent.subtype
-/

#print AffineIndependent.range /-
/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected theorem AffineIndependent.range {p : ι → P} (ha : AffineIndependent k p) :
    AffineIndependent k (fun x => x : Set.range p → P) :=
  by
  let f : Set.range p → ι := fun x => x.property.some
  have hf : ∀ x, p (f x) = x := fun x => x.property.some_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert ha.comp_embedding fe
  ext
  simp [hf]
#align affine_independent.range AffineIndependent.range
-/

#print affineIndependent_equiv /-
theorem affineIndependent_equiv {ι' : Type _} (e : ι ≃ ι') {p : ι' → P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p :=
  by
  refine' ⟨_, AffineIndependent.comp_embedding e.to_embedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.to_embedding := by ext; simp
  rw [this]
  exact h.comp_embedding e.symm.to_embedding
#align affine_independent_equiv affineIndependent_equiv
-/

#print AffineIndependent.mono /-
/-- If a set of points is affinely independent, so is any subset. -/
protected theorem AffineIndependent.mono {s t : Set P}
    (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
    AffineIndependent k (fun x => x : s → P) :=
  ha.comp_embedding (s.embeddingOfSubset t hs)
#align affine_independent.mono AffineIndependent.mono
-/

#print AffineIndependent.of_set_of_injective /-
/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
theorem AffineIndependent.of_set_of_injective {p : ι → P}
    (ha : AffineIndependent k (fun x => x : Set.range p → P)) (hi : Function.Injective p) :
    AffineIndependent k p :=
  ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun x y h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)
#align affine_independent.of_set_of_injective AffineIndependent.of_set_of_injective
-/

section Composition

variable {V₂ P₂ : Type _} [AddCommGroup V₂] [Module k V₂] [affine_space V₂ P₂]

#print AffineIndependent.of_comp /-
/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
theorem AffineIndependent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  cases' isEmpty_or_nonempty ι with h h; · haveI := h; apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linear_map_vsub] at hai 
  exact LinearIndependent.of_comp f.linear hai
#align affine_independent.of_comp AffineIndependent.of_comp
-/

#print AffineIndependent.map' /-
/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
theorem AffineIndependent.map' {p : ι → P} (hai : AffineIndependent k p) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) : AffineIndependent k (f ∘ p) :=
  by
  cases' isEmpty_or_nonempty ι with h h; · haveI := h; apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai 
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linear_map_vsub]
  have hf' : f.linear.ker = ⊥ := by rwa [LinearMap.ker_eq_bot, f.linear_injective_iff]
  exact LinearIndependent.map' hai f.linear hf'
#align affine_independent.map' AffineIndependent.map'
-/

#print AffineMap.affineIndependent_iff /-
/-- Injective affine maps preserve affine independence. -/
theorem AffineMap.affineIndependent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩
#align affine_map.affine_independent_iff AffineMap.affineIndependent_iff
-/

#print AffineEquiv.affineIndependent_iff /-
/-- Affine equivalences preserve affine independence of families of points. -/
theorem AffineEquiv.affineIndependent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.toAffineMap.affineIndependent_iff e.toEquiv.Injective
#align affine_equiv.affine_independent_iff AffineEquiv.affineIndependent_iff
-/

#print AffineEquiv.affineIndependent_set_of_eq_iff /-
/-- Affine equivalences preserve affine independence of subsets. -/
theorem AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (coe : e '' s → P₂) ↔ AffineIndependent k (coe : s → P) :=
  by
  have : e ∘ (coe : s → P) = (coe : e '' s → P₂) ∘ (e : P ≃ P₂).image s := rfl
  rw [← e.affine_independent_iff, this, affineIndependent_equiv]
#align affine_equiv.affine_independent_set_of_eq_iff AffineEquiv.affineIndependent_set_of_eq_iff
-/

end Composition

#print AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan /-
/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 ∈ affineSpan k (p '' s1))
    (hp0s2 : p0 ∈ affineSpan k (p '' s2)) : ∃ i : ι, i ∈ s1 ∩ s2 :=
  by
  rw [Set.image_eq_range] at hp0s1 hp0s2 
  rw [mem_affineSpan_iff_eq_affineCombination, ←
    Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype] at hp0s1 hp0s2 
  rcases hp0s1 with ⟨fs1, hfs1, w1, hw1, hp0s1⟩
  rcases hp0s2 with ⟨fs2, hfs2, w2, hw2, hp0s2⟩
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq] at ha 
  replace ha := ha fs1 fs2 w1 w2 hw1 hw2 (hp0s1 ▸ hp0s2)
  have hnz : ∑ i in fs1, w1 i ≠ 0 := hw1.symm ▸ one_ne_zero
  rcases Finset.exists_ne_zero_of_sum_ne_zero hnz with ⟨i, hifs1, hinz⟩
  simp_rw [← Set.indicator_of_mem (Finset.mem_coe.2 hifs1) w1, ha] at hinz 
  use i, hfs1 hifs1, hfs2 (Set.mem_of_indicator_ne_zero hinz)
#align affine_independent.exists_mem_inter_of_exists_mem_inter_affine_span AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan
-/

#print AffineIndependent.affineSpan_disjoint_of_disjoint /-
/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.affineSpan_disjoint_of_disjoint [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} (hd : Disjoint s1 s2) :
    Disjoint (affineSpan k (p '' s1) : Set P) (affineSpan k (p '' s2)) :=
  by
  refine' Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => _
  cases' ha.exists_mem_inter_of_exists_mem_inter_affine_span hp0s1 hp0s2 with i hi
  exact Set.disjoint_iff.1 hd hi
#align affine_independent.affine_span_disjoint_of_disjoint AffineIndependent.affineSpan_disjoint_of_disjoint
-/

#print AffineIndependent.mem_affineSpan_iff /-
/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
protected theorem AffineIndependent.mem_affineSpan_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∈ affineSpan k (p '' s) ↔ i ∈ s :=
  by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h 
  · exact fun h => mem_affineSpan k (Set.mem_image_of_mem p h)
#align affine_independent.mem_affine_span_iff AffineIndependent.mem_affineSpan_iff
-/

#print AffineIndependent.not_mem_affineSpan_diff /-
/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
theorem AffineIndependent.not_mem_affineSpan_diff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [ha]
#align affine_independent.not_mem_affine_span_diff AffineIndependent.not_mem_affineSpan_diff
-/

#print exists_nontrivial_relation_sum_zero_of_not_affine_ind /-
theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V}
    (h : ¬AffineIndependent k (coe : t → V)) :
    ∃ f : V → k, ∑ e in t, f e • e = 0 ∧ ∑ e in t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by classical
#align exists_nontrivial_relation_sum_zero_of_not_affine_ind exists_nontrivial_relation_sum_zero_of_not_affine_ind
-/

#print affineIndependent_iff /-
/-- Viewing a module as an affine space modelled on itself, we can characterise affine independence
in terms of linear combinations. -/
theorem affineIndependent_iff {ι} {p : ι → V} :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), s.Sum w = 0 → ∑ e in s, w e • p e = 0 → ∀ e ∈ s, w e = 0 :=
  forall₃_congr fun s w hw => by simp [s.weighted_vsub_eq_linear_combination hw]
#align affine_independent_iff affineIndependent_iff
-/

#print weightedVSub_mem_vectorSpan_pair /-
/-- Given an affinely independent family of points, a weighted subtraction lies in the
`vector_span` of two points given as affine combinations if and only if it is a weighted
subtraction with weights a multiple of the difference between the weights of the two points. -/
theorem weightedVSub_mem_vectorSpan_pair {p : ι → P} (h : AffineIndependent k p) {w w₁ w₂ : ι → k}
    {s : Finset ι} (hw : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) :
    s.weightedVSub p w ∈
        vectorSpan k ({s.affineCombination k p w₁, s.affineCombination k p w₂} : Set P) ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₁ i - w₂ i) :=
  by
  rw [mem_vectorSpan_pair]
  refine' ⟨fun h => _, fun h => _⟩
  · rcases h with ⟨r, hr⟩
    refine' ⟨r, fun i hi => _⟩
    rw [s.affine_combination_vsub, ← s.weighted_vsub_const_smul, ← sub_eq_zero, ← map_sub] at hr 
    have hw' : ∑ j in s, (r • (w₁ - w₂) - w) j = 0 := by
      simp_rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ←
        Finset.smul_sum, hw, hw₁, hw₂, sub_self]
    have hr' := h s _ hw' hr i hi
    rw [eq_comm, ← sub_eq_zero, ← smul_eq_mul]
    exact hr'
  · rcases h with ⟨r, hr⟩
    refine' ⟨r, _⟩
    let w' i := r * (w₁ i - w₂ i)
    change ∀ i ∈ s, w i = w' i at hr 
    rw [s.weighted_vsub_congr hr fun _ _ => rfl, s.affine_combination_vsub, ←
      s.weighted_vsub_const_smul]
    congr
#align weighted_vsub_mem_vector_span_pair weightedVSub_mem_vectorSpan_pair
-/

#print affineCombination_mem_affineSpan_pair /-
/-- Given an affinely independent family of points, an affine combination lies in the
span of two points given as affine combinations if and only if it is an affine combination
with weights those of one point plus a multiple of the difference between the weights of the
two points. -/
theorem affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
    (hw₂ : ∑ i in s, w₂ i = 1) :
    s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂] ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₂ i - w₁ i) + w₁ i :=
  by
  rw [← vsub_vadd (s.affine_combination k p w) (s.affine_combination k p w₁),
    AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _),
    direction_affineSpan, s.affine_combination_vsub, Set.pair_comm,
    weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp only [Pi.sub_apply, sub_eq_iff_eq_add]
  · simp_rw [Pi.sub_apply, Finset.sum_sub_distrib, hw, hw₁, sub_self]
#align affine_combination_mem_affine_span_pair affineCombination_mem_affineSpan_pair
-/

end AffineIndependent

section DivisionRing

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroup V] [Module k V]

variable [affine_space V P] {ι : Type _}

#print exists_subset_affineIndependent_affineSpan_eq_top /-
/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
theorem exists_subset_affineIndependent_affineSpan_eq_top {s : Set P}
    (h : AffineIndependent k (fun p => p : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ AffineIndependent k (fun p => p : t → P) ∧ affineSpan k t = ⊤ :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := add_torsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linear_independent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt 
    have h0 : ∀ v : V, v ∈ Basis.ofVectorSpaceIndex _ _ → v ≠ 0 := by intro v hv;
      simpa using hsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi 
    exact
      ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
  · rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁] at h 
    let bsv := Basis.extend h
    have hsvi := bsv.linear_independent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt 
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : ∀ v : V, v ∈ h.extend _ → v ≠ 0 := by intro v hv; simpa using bsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi 
    refine' ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), _, _⟩
    · refine' Set.Subset.trans _ (Set.union_subset_union_right _ (Set.image_subset _ hsv))
      simp [Set.image_image]
    · use hsvi, affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt
#align exists_subset_affine_independent_affine_span_eq_top exists_subset_affineIndependent_affineSpan_eq_top
-/

variable (k V)

/- ./././Mathport/Syntax/Translate/Basic.lean:641:2: warning: expanding binder collection (t «expr ⊆ » s) -/
#print exists_affineIndependent /-
theorem exists_affineIndependent (s : Set P) :
    ∃ (t : _) (_ : t ⊆ s), affineSpan k t = affineSpan k s ∧ AffineIndependent k (coe : t → P) :=
  by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : ∀ v : V, v ∈ b → v ≠ 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k hb₀ p] at hb₃ 
  refine' ⟨{p} ∪ Equiv.vaddConst p '' b, _, _, hb₃⟩
  · apply Set.union_subset (set.singleton_subset_iff.mpr hp)
    rwa [← (Equiv.vaddConst p).subset_symm_image b s]
  · rw [Equiv.coe_vaddConst_symm, ← vectorSpan_eq_span_vsub_set_right k hp] at hb₂ 
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by simp
      simp only [direction_affineSpan, ← hb₂, Equiv.coe_vaddConst, Set.singleton_union,
        vectorSpan_eq_span_vsub_set_right k (Set.mem_insert p _), this]
      congr
      change (Equiv.vaddConst p).symm '' insert p (Equiv.vaddConst p '' b) = _
      rw [Set.image_insert_eq, ← Set.image_comp]
      simp
    · use p
      simp only [Equiv.coe_vaddConst, Set.singleton_union, Set.mem_inter_iff, coe_affineSpan]
      exact ⟨mem_spanPoints k _ _ (Set.mem_insert p _), mem_spanPoints k _ _ hp⟩
#align exists_affine_independent exists_affineIndependent
-/

variable (k) {V P}

#print affineIndependent_of_ne /-
/-- Two different points are affinely independent. -/
theorem affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : AffineIndependent k ![p₁, p₂] :=
  by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁, p₂] 0]
  let i₁ : { x // x ≠ (0 : Fin 2) } := ⟨1, by norm_num⟩
  have he' : ∀ i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simpa using hi
  haveI : Unique { x // x ≠ (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  have hz : (![p₁, p₂] ↑default -ᵥ ![p₁, p₂] 0 : V) ≠ 0 := by rw [he' default]; simpa using h.symm
  exact linearIndependent_unique _ hz
#align affine_independent_of_ne affineIndependent_of_ne
-/

variable {k V P}

#print AffineIndependent.affineIndependent_of_not_mem_span /-
/-- If all but one point of a family are affinely independent, and that point does not lie in
the affine span of that family, the family is affinely independent. -/
theorem AffineIndependent.affineIndependent_of_not_mem_span {p : ι → P} {i : ι}
    (ha : AffineIndependent k fun x : { y // y ≠ i } => p x)
    (hi : p i ∉ affineSpan k (p '' {x | x ≠ i})) : AffineIndependent k p := by classical
#align affine_independent.affine_independent_of_not_mem_span AffineIndependent.affineIndependent_of_not_mem_span
-/

#print affineIndependent_of_ne_of_mem_of_mem_of_not_mem /-
/-- If distinct points `p₁` and `p₂` lie in `s` but `p₃` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_mem_of_mem_of_not_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₂ : p₁ ≠ p₂) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∉ s) :
    AffineIndependent k ![p₁, p₂, p₃] :=
  by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x ≠ 2 } => ![p₁, p₂, p₃] x :=
    by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3)).toEquiv]
    convert affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine' ha.affine_independent_of_not_mem_span _
  intro h
  refine' hp₃ ((AffineSubspace.le_def' _ s).1 _ p₃ h)
  simp_rw [affineSpan_le, Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro x
  fin_cases x <;> simp [hp₁, hp₂]
#align affine_independent_of_ne_of_mem_of_mem_of_not_mem affineIndependent_of_ne_of_mem_of_mem_of_not_mem
-/

#print affineIndependent_of_ne_of_mem_of_not_mem_of_mem /-
/-- If distinct points `p₁` and `p₃` lie in `s` but `p₂` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_mem_of_not_mem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₃ : p₁ ≠ p₃) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] :=
  by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert affineIndependent_of_ne_of_mem_of_mem_of_not_mem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl
#align affine_independent_of_ne_of_mem_of_not_mem_of_mem affineIndependent_of_ne_of_mem_of_not_mem_of_mem
-/

#print affineIndependent_of_ne_of_not_mem_of_mem_of_mem /-
/-- If distinct points `p₂` and `p₃` lie in `s` but `p₁` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_not_mem_of_mem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₂p₃ : p₂ ≠ p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] :=
  by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert affineIndependent_of_ne_of_mem_of_mem_of_not_mem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl
#align affine_independent_of_ne_of_not_mem_of_mem_of_mem affineIndependent_of_ne_of_not_mem_of_mem_of_mem
-/

end DivisionRing

section Ordered

variable {k : Type _} {V : Type _} {P : Type _} [LinearOrderedRing k] [AddCommGroup V]

variable [Module k V] [affine_space V P] {ι : Type _}

attribute [local instance] LinearOrderedRing.decidableLt

#print sign_eq_of_affineCombination_mem_affineSpan_pair /-
/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of two points given as affine combinations, and suppose that, for two indices, the
coefficients in the first point in the span are zero and those in the second point in the span
have the same sign. Then the coefficients in the combination lying in the span have the same
sign. -/
theorem sign_eq_of_affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1)
    (hw₂ : ∑ i in s, w₂ i = 1)
    (hs :
      s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂])
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0)
    (hij : SignType.sign (w₂ i) = SignType.sign (w₂ j)) :
    SignType.sign (w i) = SignType.sign (w j) :=
  by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs 
  rcases hs with ⟨r, hr⟩
  dsimp only at hr 
  rw [hr i hi, hr j hj, hi0, hj0, add_zero, add_zero, sub_zero, sub_zero, sign_mul, sign_mul, hij]
#align sign_eq_of_affine_combination_mem_affine_span_pair sign_eq_of_affineCombination_mem_affineSpan_pair
-/

#print sign_eq_of_affineCombination_mem_affineSpan_single_lineMap /-
/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of one point of that family and a combination of another two points of that family given
by `line_map` with coefficient between 0 and 1. Then the coefficients of those two points in the
combination lying in the span have the same sign. -/
theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι → P}
    (h : AffineIndependent k p) {w : ι → k} {s : Finset ι} (hw : ∑ i in s, w i = 1) {i₁ i₂ i₃ : ι}
    (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (h₃ : i₃ ∈ s) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {c : k} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s.affineCombination k p w ∈ line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) :
    SignType.sign (w i₂) = SignType.sign (w i₃) := by classical
#align sign_eq_of_affine_combination_mem_affine_span_single_line_map sign_eq_of_affineCombination_mem_affineSpan_single_lineMap
-/

end Ordered

namespace Affine

variable (k : Type _) {V : Type _} (P : Type _) [Ring k] [AddCommGroup V] [Module k V]

variable [affine_space V P]

#print Affine.Simplex /-
/-- A `simplex k P n` is a collection of `n + 1` affinely
independent points. -/
structure Simplex (n : ℕ) where
  points : Fin (n + 1) → P
  Independent : AffineIndependent k points
#align affine.simplex Affine.Simplex
-/

#print Affine.Triangle /-
/-- A `triangle k P` is a collection of three affinely independent points. -/
abbrev Triangle :=
  Simplex k P 2
#align affine.triangle Affine.Triangle
-/

namespace Simplex

variable {P}

#print Affine.Simplex.mkOfPoint /-
/-- Construct a 0-simplex from a point. -/
def mkOfPoint (p : P) : Simplex k P 0 :=
  ⟨fun _ => p, affineIndependent_of_subsingleton k _⟩
#align affine.simplex.mk_of_point Affine.Simplex.mkOfPoint
-/

#print Affine.Simplex.mkOfPoint_points /-
/-- The point in a simplex constructed with `mk_of_point`. -/
@[simp]
theorem mkOfPoint_points (p : P) (i : Fin 1) : (mkOfPoint k p).points i = p :=
  rfl
#align affine.simplex.mk_of_point_points Affine.Simplex.mkOfPoint_points
-/

instance [Inhabited P] : Inhabited (Simplex k P 0) :=
  ⟨mkOfPoint k default⟩

#print Affine.Simplex.nonempty /-
instance nonempty : Nonempty (Simplex k P 0) :=
  ⟨mkOfPoint k <| AddTorsor.nonempty.some⟩
#align affine.simplex.nonempty Affine.Simplex.nonempty
-/

variable {k V}

#print Affine.Simplex.ext /-
/-- Two simplices are equal if they have the same points. -/
@[ext]
theorem ext {n : ℕ} {s1 s2 : Simplex k P n} (h : ∀ i, s1.points i = s2.points i) : s1 = s2 :=
  by
  cases s1
  cases s2
  congr with i
  exact h i
#align affine.simplex.ext Affine.Simplex.ext
-/

#print Affine.Simplex.ext_iff /-
/-- Two simplices are equal if and only if they have the same points. -/
theorem ext_iff {n : ℕ} (s1 s2 : Simplex k P n) : s1 = s2 ↔ ∀ i, s1.points i = s2.points i :=
  ⟨fun h _ => h ▸ rfl, ext⟩
#align affine.simplex.ext_iff Affine.Simplex.ext_iff
-/

#print Affine.Simplex.face /-
/-- A face of a simplex is a simplex with the given subset of
points. -/
def face {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ} (h : fs.card = m + 1) :
    Simplex k P m :=
  ⟨s.points ∘ fs.orderEmbOfFin h, s.Independent.comp_embedding (fs.orderEmbOfFin h).toEmbedding⟩
#align affine.simplex.face Affine.Simplex.face
-/

#print Affine.Simplex.face_points /-
/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) (i : Fin (m + 1)) :
    (s.face h).points i = s.points (fs.orderEmbOfFin h i) :=
  rfl
#align affine.simplex.face_points Affine.Simplex.face_points
-/

#print Affine.Simplex.face_points' /-
/-- The points of a face of a simplex are given by `mono_of_fin`. -/
theorem face_points' {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) : (s.face h).points = s.points ∘ fs.orderEmbOfFin h :=
  rfl
#align affine.simplex.face_points' Affine.Simplex.face_points'
-/

#print Affine.Simplex.face_eq_mkOfPoint /-
/-- A single-point face equals the 0-simplex constructed with
`mk_of_point`. -/
@[simp]
theorem face_eq_mkOfPoint {n : ℕ} (s : Simplex k P n) (i : Fin (n + 1)) :
    s.face (Finset.card_singleton i) = mkOfPoint k (s.points i) := by ext; simp [face_points]
#align affine.simplex.face_eq_mk_of_point Affine.Simplex.face_eq_mkOfPoint
-/

#print Affine.Simplex.range_face_points /-
/-- The set of points of a face. -/
@[simp]
theorem range_face_points {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) : Set.range (s.face h).points = s.points '' ↑fs := by
  rw [face_points', Set.range_comp, Finset.range_orderEmbOfFin]
#align affine.simplex.range_face_points Affine.Simplex.range_face_points
-/

#print Affine.Simplex.reindex /-
/-- Remap a simplex along an `equiv` of index types. -/
@[simps]
def reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) : Simplex k P n :=
  ⟨s.points ∘ e.symm, (affineIndependent_equiv e.symm).2 s.Independent⟩
#align affine.simplex.reindex Affine.Simplex.reindex
-/

#print Affine.Simplex.reindex_refl /-
/-- Reindexing by `equiv.refl` yields the original simplex. -/
@[simp]
theorem reindex_refl {n : ℕ} (s : Simplex k P n) : s.reindex (Equiv.refl (Fin (n + 1))) = s :=
  ext fun _ => rfl
#align affine.simplex.reindex_refl Affine.Simplex.reindex_refl
-/

#print Affine.Simplex.reindex_trans /-
/-- Reindexing by the composition of two equivalences is the same as reindexing twice. -/
@[simp]
theorem reindex_trans {n₁ n₂ n₃ : ℕ} (e₁₂ : Fin (n₁ + 1) ≃ Fin (n₂ + 1))
    (e₂₃ : Fin (n₂ + 1) ≃ Fin (n₃ + 1)) (s : Simplex k P n₁) :
    s.reindex (e₁₂.trans e₂₃) = (s.reindex e₁₂).reindex e₂₃ :=
  rfl
#align affine.simplex.reindex_trans Affine.Simplex.reindex_trans
-/

#print Affine.Simplex.reindex_reindex_symm /-
/-- Reindexing by an equivalence and its inverse yields the original simplex. -/
@[simp]
theorem reindex_reindex_symm {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).reindex e.symm = s := by rw [← reindex_trans, Equiv.self_trans_symm, reindex_refl]
#align affine.simplex.reindex_reindex_symm Affine.Simplex.reindex_reindex_symm
-/

#print Affine.Simplex.reindex_symm_reindex /-
/-- Reindexing by the inverse of an equivalence and that equivalence yields the original simplex. -/
@[simp]
theorem reindex_symm_reindex {m n : ℕ} (s : Simplex k P m) (e : Fin (n + 1) ≃ Fin (m + 1)) :
    (s.reindex e.symm).reindex e = s := by rw [← reindex_trans, Equiv.symm_trans_self, reindex_refl]
#align affine.simplex.reindex_symm_reindex Affine.Simplex.reindex_symm_reindex
-/

#print Affine.Simplex.reindex_range_points /-
/-- Reindexing a simplex produces one with the same set of points. -/
@[simp]
theorem reindex_range_points {m n : ℕ} (s : Simplex k P m) (e : Fin (m + 1) ≃ Fin (n + 1)) :
    Set.range (s.reindex e).points = Set.range s.points := by
  rw [reindex, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
#align affine.simplex.reindex_range_points Affine.Simplex.reindex_range_points
-/

end Simplex

end Affine

namespace Affine

namespace Simplex

variable {k : Type _} {V : Type _} {P : Type _} [DivisionRing k] [AddCommGroup V] [Module k V]
  [affine_space V P]

#print Affine.Simplex.face_centroid_eq_centroid /-
/-- The centroid of a face of a simplex as the centroid of a subset of
the points. -/
@[simp]
theorem face_centroid_eq_centroid {n : ℕ} (s : Simplex k P n) {fs : Finset (Fin (n + 1))} {m : ℕ}
    (h : fs.card = m + 1) : Finset.univ.centroid k (s.face h).points = fs.centroid k s.points :=
  by
  convert (finset.univ.centroid_map k (fs.order_emb_of_fin h).toEmbedding s.points).symm
  rw [← Finset.coe_inj, Finset.coe_map, Finset.coe_univ, Set.image_univ]
  simp
#align affine.simplex.face_centroid_eq_centroid Affine.Simplex.face_centroid_eq_centroid
-/

#print Affine.Simplex.centroid_eq_iff /-
/-- Over a characteristic-zero division ring, the centroids given by
two subsets of the points of a simplex are equal if and only if those
faces are given by the same subset of points. -/
@[simp]
theorem centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n) {fs₁ fs₂ : Finset (Fin (n + 1))}
    {m₁ m₂ : ℕ} (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
    fs₁.centroid k s.points = fs₂.centroid k s.points ↔ fs₁ = fs₂ :=
  by
  refine' ⟨fun h => _, congr_arg _⟩
  rw [Finset.centroid_eq_affineCombination_fintype, Finset.centroid_eq_affineCombination_fintype] at
    h 
  have ha :=
    (affineIndependent_iff_indicator_eq_of_affineCombination_eq k s.points).1 s.independent _ _ _ _
      (fs₁.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₁)
      (fs₂.sum_centroid_weights_indicator_eq_one_of_card_eq_add_one k h₂) h
  simp_rw [Finset.coe_univ, Set.indicator_univ, Function.funext_iff,
    Finset.centroidWeightsIndicator_def, Finset.centroidWeights, h₁, h₂] at ha 
  ext i
  specialize ha i
  have key : ∀ n : ℕ, (n : k) + 1 ≠ 0 := fun n h => by norm_cast at h 
  -- we should be able to golf this to `refine ⟨λ hi, decidable.by_contradiction (λ hni, _), ...⟩`,
      -- but for some unknown reason it doesn't work.
      constructor <;>
      intro hi <;>
    by_contra hni
  · simpa [hni, hi, key] using ha
  · simpa [hni, hi, key] using ha.symm
#align affine.simplex.centroid_eq_iff Affine.Simplex.centroid_eq_iff
-/

#print Affine.Simplex.face_centroid_eq_iff /-
/-- Over a characteristic-zero division ring, the centroids of two
faces of a simplex are equal if and only if those faces are given by
the same subset of points. -/
theorem face_centroid_eq_iff [CharZero k] {n : ℕ} (s : Simplex k P n)
    {fs₁ fs₂ : Finset (Fin (n + 1))} {m₁ m₂ : ℕ} (h₁ : fs₁.card = m₁ + 1) (h₂ : fs₂.card = m₂ + 1) :
    Finset.univ.centroid k (s.face h₁).points = Finset.univ.centroid k (s.face h₂).points ↔
      fs₁ = fs₂ :=
  by
  rw [face_centroid_eq_centroid, face_centroid_eq_centroid]
  exact s.centroid_eq_iff h₁ h₂
#align affine.simplex.face_centroid_eq_iff Affine.Simplex.face_centroid_eq_iff
-/

#print Affine.Simplex.centroid_eq_of_range_eq /-
/-- Two simplices with the same points have the same centroid. -/
theorem centroid_eq_of_range_eq {n : ℕ} {s₁ s₂ : Simplex k P n}
    (h : Set.range s₁.points = Set.range s₂.points) :
    Finset.univ.centroid k s₁.points = Finset.univ.centroid k s₂.points :=
  by
  rw [← Set.image_univ, ← Set.image_univ, ← Finset.coe_univ] at h 
  exact
    finset.univ.centroid_eq_of_inj_on_of_image_eq k _
      (fun _ _ _ _ he => AffineIndependent.injective s₁.independent he)
      (fun _ _ _ _ he => AffineIndependent.injective s₂.independent he) h
#align affine.simplex.centroid_eq_of_range_eq Affine.Simplex.centroid_eq_of_range_eq
-/

end Simplex

end Affine

