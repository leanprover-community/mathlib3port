import Mathbin.LinearAlgebra.AffineSpace.Independent

/-!
# Barycentric coordinates

Suppose `P` is an affine space modelled on the module `V` over the ring `k`, and `p : ι → P` is an
affine-independent family of points spanning `P`. Given this data, each point `q : P` may be written
uniquely as an affine combination: `q = w₀ p₀ + w₁ p₁ + ⋯` for some (finitely-supported) weights
`wᵢ`. For each `i : ι`, we thus have an affine map `P →ᵃ[k] k`, namely `q ↦ wᵢ`. This family of
maps is known as the family of barycentric coordinates. It is defined in this file.

## The construction

Fixing `i : ι`, and allowing `j : ι` to range over the values `j ≠ i`, we obtain a basis `bᵢ` of `V`
defined by `bᵢ j = p j -ᵥ p i`. Let `fᵢ j : V →ₗ[k] k` be the corresponding dual basis and let
`fᵢ = ∑ j, fᵢ j : V →ₗ[k] k` be the corresponding "sum of all coordinates" form. Then the `i`th
barycentric coordinate of `q : P` is `1 - fᵢ (q -ᵥ p i)`.

## Main definitions

 * `barycentric_coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `barycentric_coord_apply_eq`: the behaviour of `barycentric_coord i` on `p i`.
 * `barycentric_coord_apply_neq`: the behaviour of `barycentric_coord i` on `p j` when `j ≠ i`.
 * `barycentric_coord_apply`: the behaviour of `barycentric_coord i` on `p j` for general `j`.
 * `barycentric_coord_apply_combination`: the characterisation of `barycentric_coord i` in terms
    of affine combinations, i.e., `barycentric_coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/


open_locale Affine BigOperators

open Set

universe u₁ u₂ u₃ u₄

variable{ι : Type u₁}{k : Type u₂}{V : Type u₃}{P : Type u₄}

variable[Ringₓ k][AddCommGroupₓ V][Module k V][affine_space V P]

variable{p : ι → P}(h_ind : AffineIndependent k p)(h_tot : affineSpan k (range p) = ⊤)

include V h_ind h_tot

/-- Given an affine-independent family of points spanning the point space `P`, if we single out one
member of the family, we obtain a basis for the model space `V`.

The basis correpsonding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}` and its
`j`th element is `p j -ᵥ p i`. (See `basis_of_aff_ind_span_eq_top_apply`.) -/
noncomputable def basisOfAffIndSpanEqTop (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affine_independent_iff_linear_independent_vsub k p i).mp h_ind)
    (by 
      suffices  : Submodule.span k (range fun j : { x // x ≠ i } => p («expr↑ » j) -ᵥ p i) = vectorSpan k (range p)
      ·
        rw [this, ←direction_affine_span, h_tot, AffineSubspace.direction_top]
      convRHS => rw [←image_univ]
      rw [vector_span_image_eq_span_vsub_set_right_ne k p (mem_univ i)]
      congr 
      ext v 
      simp )

local notation "basis_of" => basisOfAffIndSpanEqTop h_ind h_tot

@[simp]
theorem basis_of_aff_ind_span_eq_top_apply (i : ι) (j : { j : ι // j ≠ i }) : basis_of i j = p («expr↑ » j) -ᵥ p i :=
  by 
    simp [basisOfAffIndSpanEqTop]

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def barycentricCoord (i : ι) : P →ᵃ[k] k :=
  { toFun := fun q => 1 - (basis_of i).sumCoords (q -ᵥ p i), linear := -(basis_of i).sumCoords,
    map_vadd' :=
      fun q v =>
        by 
          rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply, sub_add_eq_sub_sub_swap, add_commₓ,
            sub_eq_add_neg] }

@[simp]
theorem barycentric_coord_apply_eq (i : ι) : barycentricCoord h_ind h_tot i (p i) = 1 :=
  by 
    simp only [barycentricCoord, Basis.coe_sum_coords, LinearEquiv.map_zero, LinearEquiv.coe_coe, sub_zero,
      AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]

@[simp]
theorem barycentric_coord_apply_neq (i j : ι) (h : j ≠ i) : barycentricCoord h_ind h_tot i (p j) = 0 :=
  by 
    rw [barycentricCoord, AffineMap.coe_mk, ←Subtype.coe_mk j h,
      ←basis_of_aff_ind_span_eq_top_apply h_ind h_tot i ⟨j, h⟩, Basis.sum_coords_self_apply, sub_self]

theorem barycentric_coord_apply [DecidableEq ι] (i j : ι) :
  barycentricCoord h_ind h_tot i (p j) = if i = j then 1 else 0 :=
  by 
    cases eq_or_ne i j <;> simp [h.symm]
    simp [h]

@[simp]
theorem barycentric_coord_apply_combination_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
  barycentricCoord h_ind h_tot i (s.affine_combination p w) = w i :=
  by 
    classical 
    simp only [barycentric_coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_true, hw, mul_boole,
      Function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination p w hw]

@[simp]
theorem barycentric_coord_apply_combination_of_not_mem {s : Finset ι} {i : ι} (hi : i ∉ s) {w : ι → k}
  (hw : s.sum w = 1) : barycentricCoord h_ind h_tot i (s.affine_combination p w) = 0 :=
  by 
    classical 
    simp only [barycentric_coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_false, hw, mul_boole,
      Function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination p w hw]

@[simp]
theorem sum_barycentric_coord_apply_eq_one [Fintype ι] (q : P) : (∑i, barycentricCoord h_ind h_tot i q) = 1 :=
  by 
    have hq : q ∈ affineSpan k (range p)
    ·
      rw [h_tot]
      exact AffineSubspace.mem_top k V q 
    obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq 
    convert hw 
    ext i 
    exact barycentric_coord_apply_combination_of_mem h_ind h_tot (Finset.mem_univ i) hw

@[simp]
theorem affine_combination_barycentric_coord_eq_self [Fintype ι] (q : P) :
  (Finset.univ.affineCombination p fun i => barycentricCoord h_ind h_tot i q) = q :=
  by 
    have hq : q ∈ affineSpan k (range p)
    ·
      rw [h_tot]
      exact AffineSubspace.mem_top k V q 
    obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq 
    congr 
    ext i 
    exact barycentric_coord_apply_combination_of_mem h_ind h_tot (Finset.mem_univ i) hw

@[simp]
theorem coe_barycentric_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) :
  (barycentricCoord h_ind h_tot i : P → k) = 1 :=
  by 
    ext q 
    have hp : (range p).Subsingleton
    ·
      rw [←image_univ]
      apply subsingleton.image 
      apply subsingleton_of_subsingleton 
    haveI  := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp h_tot 
    let s : Finset ι := {i}
    have hi : i ∈ s
    ·
      simp 
    have hw : s.sum (Function.const ι (1 : k)) = 1
    ·
      simp 
    have hq : q = s.affine_combination p (Function.const ι (1 : k))
    ·
      simp 
    rw [Pi.one_apply, hq, barycentric_coord_apply_combination_of_mem h_ind h_tot hi hw]

theorem surjective_barycentric_coord [Nontrivial ι] (i : ι) : Function.Surjective$ barycentricCoord h_ind h_tot i :=
  by 
    classical 
    intro x 
    obtain ⟨j, hij⟩ := exists_ne i 
    let s : Finset ι := {i, j}
    have hi : i ∈ s
    ·
      simp 
    have hj : j ∈ s
    ·
      simp 
    let w : ι → k := fun j' => if j' = i then x else 1 - x 
    have hw : s.sum w = 1
    ·
      simp [hij, Finset.sum_ite, Finset.filter_insert, Finset.filter_eq']
    use s.affine_combination p w 
    simp [barycentric_coord_apply_combination_of_mem h_ind h_tot hi hw]

