/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash

! This file was ported from Lean 3 source module linear_algebra.affine_space.basis
! leanprover-community/mathlib commit d4f69d96f3532729da8ebb763f4bc26fcf640f06
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.AffineSpace.Independent
import Mathbin.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathbin.LinearAlgebra.Determinant

/-!
# Affine bases and barycentric coordinates

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

 * `affine_basis`: a structure representing an affine basis of an affine space.
 * `affine_basis.coord`: the map `P →ᵃ[k] k` corresponding to `i : ι`.
 * `affine_basis.coord_apply_eq`: the behaviour of `affine_basis.coord i` on `p i`.
 * `affine_basis.coord_apply_neq`: the behaviour of `affine_basis.coord i` on `p j` when `j ≠ i`.
 * `affine_basis.coord_apply`: the behaviour of `affine_basis.coord i` on `p j` for general `j`.
 * `affine_basis.coord_apply_combination`: the characterisation of `affine_basis.coord i` in terms
    of affine combinations, i.e., `affine_basis.coord i (w₀ p₀ + w₁ p₁ + ⋯) = wᵢ`.

## TODO

 * Construct the affine equivalence between `P` and `{ f : ι →₀ k | f.sum = 1 }`.

-/


open Affine BigOperators Matrix

open Set

universe u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroup V]
  [affine_space V P] [Ring k] [Module k V] where
  points : ι → P
  ind : AffineIndependent k points
  tot : affineSpan k (range points) = ⊤
#align affine_basis AffineBasis

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroup V] [affine_space V P]

namespace AffineBasis

section Ring

variable [Ring k] [Module k V] (b : AffineBasis ι k P)

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨{  points := id
      ind := affine_independent_of_subsingleton k id
      tot := by simp }⟩

include b

protected theorem nonempty : Nonempty ι :=
  not_isEmpty_iff.mp fun hι => by
    simpa only [@range_eq_empty _ _ hι, AffineSubspace.span_empty, bot_ne_top] using b.tot
#align affine_basis.nonempty AffineBasis.nonempty

/-- Composition of an affine basis and an equivalence of index types. -/
def compEquiv {ι'} (e : ι' ≃ ι) : AffineBasis ι' k P :=
  ⟨b.points ∘ e, b.ind.comp_embedding e.toEmbedding, by
    rw [e.surjective.range_comp]
    exact b.3⟩
#align affine_basis.comp_equiv AffineBasis.compEquiv

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis correpsonding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `points j -ᵥ points i`. (See `basis_of_apply`.) -/
noncomputable def basisOf (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affine_independent_iff_linear_independent_vsub k b.points i).mp b.ind)
    (by
      suffices
        Submodule.span k (range fun j : { x // x ≠ i } => b.points ↑j -ᵥ b.points i) =
          vectorSpan k (range b.points)
        by 
        rw [this, ← direction_affine_span, b.tot, AffineSubspace.direction_top]
        exact le_rfl
      conv_rhs => rw [← image_univ]
      rw [vector_span_image_eq_span_vsub_set_right_ne k b.points (mem_univ i)]
      congr
      ext v
      simp)
#align affine_basis.basis_of AffineBasis.basisOf

@[simp]
theorem basis_of_apply (i : ι) (j : { j : ι // j ≠ i }) :
    b.basisOf i j = b.points ↑j -ᵥ b.points i := by simp [basis_of]
#align affine_basis.basis_of_apply AffineBasis.basis_of_apply

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) :
    P →ᵃ[k] k where 
  toFun q := 1 - (b.basisOf i).sumCoords (q -ᵥ b.points i)
  linear := -(b.basisOf i).sumCoords
  map_vadd' q v := by
    rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply,
      sub_add_eq_sub_sub_swap, add_comm, sub_eq_add_neg]
#align affine_basis.coord AffineBasis.coord

@[simp]
theorem linear_eq_sum_coords (i : ι) : (b.Coord i).linear = -(b.basisOf i).sumCoords :=
  rfl
#align affine_basis.linear_eq_sum_coords AffineBasis.linear_eq_sum_coords

@[simp]
theorem coord_apply_eq (i : ι) : b.Coord i (b.points i) = 1 := by
  simp only [coord, Basis.coe_sum_coords, LinearEquiv.map_zero, LinearEquiv.coe_coe, sub_zero,
    AffineMap.coe_mk, Finsupp.sum_zero_index, vsub_self]
#align affine_basis.coord_apply_eq AffineBasis.coord_apply_eq

@[simp]
theorem coord_apply_neq (i j : ι) (h : j ≠ i) : b.Coord i (b.points j) = 0 := by
  rw [coord, AffineMap.coe_mk, ← Subtype.coe_mk j h, ← b.basis_of_apply i ⟨j, h⟩,
    Basis.sum_coords_self_apply, sub_self]
#align affine_basis.coord_apply_neq AffineBasis.coord_apply_neq

theorem coord_apply [DecidableEq ι] (i j : ι) : b.Coord i (b.points j) = if i = j then 1 else 0 :=
  by 
  cases eq_or_ne i j <;> simp [h.symm]
  simp [h]
#align affine_basis.coord_apply AffineBasis.coord_apply

@[simp]
theorem coord_apply_combination_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s) {w : ι → k}
    (hw : s.Sum w = 1) : b.Coord i (s.affineCombination b.points w) = w i := by
  classical simp only [coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_true,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affine_combination b.points w hw]
#align affine_basis.coord_apply_combination_of_mem AffineBasis.coord_apply_combination_of_mem

@[simp]
theorem coord_apply_combination_of_not_mem {s : Finset ι} {i : ι} (hi : i ∉ s) {w : ι → k}
    (hw : s.Sum w = 1) : b.Coord i (s.affineCombination b.points w) = 0 := by
  classical simp only [coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_false,
      mul_boole, hw, Function.comp_apply, smul_eq_mul, s.sum_ite_eq,
      s.map_affine_combination b.points w hw]
#align
  affine_basis.coord_apply_combination_of_not_mem AffineBasis.coord_apply_combination_of_not_mem

@[simp]
theorem sum_coord_apply_eq_one [Fintype ι] (q : P) : (∑ i, b.Coord i q) = 1 := by
  have hq : q ∈ affineSpan k (range b.points) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq
  convert hw
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
#align affine_basis.sum_coord_apply_eq_one AffineBasis.sum_coord_apply_eq_one

@[simp]
theorem affine_combination_coord_eq_self [Fintype ι] (q : P) :
    (Finset.univ.affineCombination b.points fun i => b.Coord i q) = q := by
  have hq : q ∈ affineSpan k (range b.points) := by
    rw [b.tot]
    exact AffineSubspace.mem_top k V q
  obtain ⟨w, hw, rfl⟩ := eq_affine_combination_of_mem_affine_span_of_fintype hq
  congr
  ext i
  exact b.coord_apply_combination_of_mem (Finset.mem_univ i) hw
#align affine_basis.affine_combination_coord_eq_self AffineBasis.affine_combination_coord_eq_self

/-- A variant of `affine_basis.affine_combination_coord_eq_self` for the special case when the
affine space is a module so we can talk about linear combinations. -/
@[simp]
theorem linear_combination_coord_eq_self [Fintype ι] (b : AffineBasis ι k V) (v : V) :
    (∑ i, b.Coord i v • b.points i) = v := by
  have hb := b.affine_combination_coord_eq_self v
  rwa [finset.univ.affine_combination_eq_linear_combination _ _ (b.sum_coord_apply_eq_one v)] at hb
#align affine_basis.linear_combination_coord_eq_self AffineBasis.linear_combination_coord_eq_self

theorem ext_elem [Fintype ι] {q₁ q₂ : P} (h : ∀ i, b.Coord i q₁ = b.Coord i q₂) : q₁ = q₂ := by
  rw [← b.affine_combination_coord_eq_self q₁, ← b.affine_combination_coord_eq_self q₂]
  simp only [h]
#align affine_basis.ext_elem AffineBasis.ext_elem

@[simp]
theorem coe_coord_of_subsingleton_eq_one [Subsingleton ι] (i : ι) : (b.Coord i : P → k) = 1 := by
  ext q
  have hp : (range b.points).Subsingleton := by
    rw [← image_univ]
    apply subsingleton.image
    apply subsingleton_of_subsingleton
  haveI := AffineSubspace.subsingleton_of_subsingleton_span_eq_top hp b.tot
  let s : Finset ι := {i}
  have hi : i ∈ s := by simp
  have hw : s.sum (Function.const ι (1 : k)) = 1 := by simp
  have hq : q = s.affine_combination b.points (Function.const ι (1 : k)) := by simp
  rw [Pi.one_apply, hq, b.coord_apply_combination_of_mem hi hw]
#align affine_basis.coe_coord_of_subsingleton_eq_one AffineBasis.coe_coord_of_subsingleton_eq_one

theorem surjective_coord [Nontrivial ι] (i : ι) : Function.Surjective <| b.Coord i := by
  classical 
    intro x
    obtain ⟨j, hij⟩ := exists_ne i
    let s : Finset ι := {i, j}
    have hi : i ∈ s := by simp
    have hj : j ∈ s := by simp
    let w : ι → k := fun j' => if j' = i then x else 1 - x
    have hw : s.sum w = 1 := by simp [hij, Finset.sum_ite, Finset.filter_insert, Finset.filter_eq']
    use s.affine_combination b.points w
    simp [b.coord_apply_combination_of_mem hi hw]
#align affine_basis.surjective_coord AffineBasis.surjective_coord

/-- Barycentric coordinates as an affine map. -/
noncomputable def coords :
    P →ᵃ[k] ι → k where 
  toFun q i := b.Coord i q
  linear :=
    { toFun := fun v i => -(b.basisOf i).sumCoords v
      map_add' := fun v w => by 
        ext i
        simp only [LinearMap.map_add, Pi.add_apply, neg_add]
      map_smul' := fun t v => by 
        ext i
        simpa only [LinearMap.map_smul, Pi.smul_apply, smul_neg] }
  map_vadd' p v := by 
    ext i
    simp only [linear_eq_sum_coords, LinearMap.coe_mk, LinearMap.neg_apply, Pi.vadd_apply',
      AffineMap.map_vadd]
#align affine_basis.coords AffineBasis.coords

@[simp]
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.Coord i q :=
  rfl
#align affine_basis.coords_apply AffineBasis.coords_apply

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `basis.to_matrix`. -/
noncomputable def toMatrix {ι' : Type _} (q : ι' → P) : Matrix ι' ι k := fun i j => b.Coord j (q i)
#align affine_basis.to_matrix AffineBasis.toMatrix

@[simp]
theorem to_matrix_apply {ι' : Type _} (q : ι' → P) (i : ι') (j : ι) :
    b.toMatrix q i j = b.Coord j (q i) :=
  rfl
#align affine_basis.to_matrix_apply AffineBasis.to_matrix_apply

@[simp]
theorem to_matrix_self [DecidableEq ι] : b.toMatrix b.points = (1 : Matrix ι ι k) := by
  ext (i j)
  rw [to_matrix_apply, coord_apply, Matrix.one_eq_pi_single, Pi.single_apply]
#align affine_basis.to_matrix_self AffineBasis.to_matrix_self

variable {ι' : Type _} [Fintype ι'] [Fintype ι] (b₂ : AffineBasis ι k P)

theorem to_matrix_row_sum_one {ι' : Type _} (q : ι' → P) (i : ι') : (∑ j, b.toMatrix q i j) = 1 :=
  by simp
#align affine_basis.to_matrix_row_sum_one AffineBasis.to_matrix_row_sum_one

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
theorem affine_independent_of_to_matrix_right_inv [DecidableEq ι'] (p : ι' → P) {A : Matrix ι ι' k}
    (hA : b.toMatrix p ⬝ A = 1) : AffineIndependent k p := by
  rw [affine_independent_iff_eq_of_fintype_affine_combination_eq]
  intro w₁ w₂ hw₁ hw₂ hweq
  have hweq' : (b.to_matrix p).vecMul w₁ = (b.to_matrix p).vecMul w₂ := by
    ext j
    change (∑ i, w₁ i • b.coord j (p i)) = ∑ i, w₂ i • b.coord j (p i)
    rw [← finset.univ.affine_combination_eq_linear_combination _ _ hw₁, ←
      finset.univ.affine_combination_eq_linear_combination _ _ hw₂, ←
      finset.univ.map_affine_combination p w₁ hw₁, ← finset.univ.map_affine_combination p w₂ hw₂,
      hweq]
  replace hweq' := congr_arg (fun w => A.vec_mul w) hweq'
  simpa only [Matrix.vec_mul_vec_mul, ← Matrix.mul_eq_mul, hA, Matrix.vec_mul_one] using hweq'
#align
  affine_basis.affine_independent_of_to_matrix_right_inv AffineBasis.affine_independent_of_to_matrix_right_inv

/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the entire space. -/
theorem affine_span_eq_top_of_to_matrix_left_inv [DecidableEq ι] [Nontrivial k] (p : ι' → P)
    {A : Matrix ι ι' k} (hA : A ⬝ b.toMatrix p = 1) : affineSpan k (range p) = ⊤ := by
  suffices ∀ i, b.points i ∈ affineSpan k (range p) by
    rw [eq_top_iff, ← b.tot, affine_span_le]
    rintro q ⟨i, rfl⟩
    exact this i
  intro i
  have hAi : (∑ j, A i j) = 1 := by
    calc
      (∑ j, A i j) = ∑ j, A i j * ∑ l, b.to_matrix p j l := by simp
      _ = ∑ j, ∑ l, A i j * b.to_matrix p j l := by simp_rw [Finset.mul_sum]
      _ = ∑ l, ∑ j, A i j * b.to_matrix p j l := by rw [Finset.sum_comm]
      _ = ∑ l, (A ⬝ b.to_matrix p) i l := rfl
      _ = 1 := by simp [hA, Matrix.one_apply, Finset.filter_eq]
      
  have hbi : b.points i = finset.univ.affine_combination p (A i) := by
    apply b.ext_elem
    intro j
    rw [b.coord_apply, finset.univ.map_affine_combination _ _ hAi,
      finset.univ.affine_combination_eq_linear_combination _ _ hAi]
    change _ = (A ⬝ b.to_matrix p) i j
    simp_rw [hA, Matrix.one_apply, @eq_comm _ i j]
  rw [hbi]
  exact affine_combination_mem_affine_span hAi p
#align
  affine_basis.affine_span_eq_top_of_to_matrix_left_inv AffineBasis.affine_span_eq_top_of_to_matrix_left_inv

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_inv_mul_affine_basis_to_matrix`. -/
@[simp]
theorem to_matrix_vec_mul_coords (x : P) :
    (b.toMatrix b₂.points).vecMul (b₂.coords x) = b.coords x := by
  ext j
  change _ = b.coord j x
  conv_rhs => rw [← b₂.affine_combination_coord_eq_self x]
  rw [Finset.map_affine_combination _ _ _ (b₂.sum_coord_apply_eq_one x)]
  simp [Matrix.vecMul, Matrix.dotProduct, to_matrix_apply, coords]
#align affine_basis.to_matrix_vec_mul_coords AffineBasis.to_matrix_vec_mul_coords

variable [DecidableEq ι]

theorem to_matrix_mul_to_matrix : b.toMatrix b₂.points ⬝ b₂.toMatrix b.points = 1 := by
  ext (l m)
  change (b₂.to_matrix b.points).vecMul (b.coords (b₂.points l)) m = _
  rw [to_matrix_vec_mul_coords, coords_apply, ← to_matrix_apply, to_matrix_self]
#align affine_basis.to_matrix_mul_to_matrix AffineBasis.to_matrix_mul_to_matrix

theorem is_unit_to_matrix : IsUnit (b.toMatrix b₂.points) :=
  ⟨{  val := b.toMatrix b₂.points
      inv := b₂.toMatrix b.points
      val_inv := b.to_matrix_mul_to_matrix b₂
      inv_val := b₂.to_matrix_mul_to_matrix b }, rfl⟩
#align affine_basis.is_unit_to_matrix AffineBasis.is_unit_to_matrix

theorem is_unit_to_matrix_iff [Nontrivial k] (p : ι → P) :
    IsUnit (b.toMatrix p) ↔ AffineIndependent k p ∧ affineSpan k (range p) = ⊤ := by
  constructor
  · rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.to_matrix p⟩
    rw [Matrix.mul_eq_mul] at hA hA'
    exact
      ⟨b.affine_independent_of_to_matrix_right_inv p hA,
        b.affine_span_eq_top_of_to_matrix_left_inv p hA'⟩
  · rintro ⟨h_tot, h_ind⟩
    let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
    change IsUnit (b.to_matrix b'.points)
    exact b.is_unit_to_matrix b'
#align affine_basis.is_unit_to_matrix_iff AffineBasis.is_unit_to_matrix_iff

end Ring

section CommRing

variable [CommRing k] [Module k V] [DecidableEq ι] [Fintype ι]

variable (b b₂ : AffineBasis ι k P)

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_vec_mul_coords`. -/
@[simp]
theorem to_matrix_inv_vec_mul_to_matrix (x : P) :
    (b.toMatrix b₂.points)⁻¹.vecMul (b.coords x) = b₂.coords x := by
  have hu := b.is_unit_to_matrix b₂
  rw [Matrix.is_unit_iff_is_unit_det] at hu
  rw [← b.to_matrix_vec_mul_coords b₂, Matrix.vec_mul_vec_mul, Matrix.mul_nonsing_inv _ hu,
    Matrix.vec_mul_one]
#align affine_basis.to_matrix_inv_vec_mul_to_matrix AffineBasis.to_matrix_inv_vec_mul_to_matrix

/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
theorem det_smul_coords_eq_cramer_coords (x : P) :
    (b.toMatrix b₂.points).det • b₂.coords x = (b.toMatrix b₂.points)ᵀ.cramer (b.coords x) := by
  have hu := b.is_unit_to_matrix b₂
  rw [Matrix.is_unit_iff_is_unit_det] at hu
  rw [← b.to_matrix_inv_vec_mul_to_matrix, Matrix.det_smul_inv_vec_mul_eq_cramer_transpose _ _ hu]
#align affine_basis.det_smul_coords_eq_cramer_coords AffineBasis.det_smul_coords_eq_cramer_coords

end CommRing

section DivisionRing

variable [DivisionRing k] [Module k V]

include V

protected theorem finite_dimensional [Finite ι] (b : AffineBasis ι k P) : FiniteDimensional k V :=
  let ⟨i⟩ := b.Nonempty
  FiniteDimensional.of_fintype_basis (b.basisOf i)
#align affine_basis.finite_dimensional AffineBasis.finite_dimensional

protected theorem finite [FiniteDimensional k V] (b : AffineBasis ι k P) : Finite ι :=
  finite_of_fin_dim_affine_independent k b.ind
#align affine_basis.finite AffineBasis.finite

protected theorem finite_set [FiniteDimensional k V] {s : Set ι} (b : AffineBasis s k P) :
    s.Finite :=
  finite_set_of_fin_dim_affine_independent k b.ind
#align affine_basis.finite_set AffineBasis.finite_set

@[simp]
theorem coord_apply_centroid [CharZero k] (b : AffineBasis ι k P) {s : Finset ι} {i : ι}
    (hi : i ∈ s) : b.Coord i (s.centroid k b.points) = (s.card : k)⁻¹ := by
  rw [Finset.centroid,
    b.coord_apply_combination_of_mem hi (s.sum_centroid_weights_eq_one_of_nonempty _ ⟨i, hi⟩),
    Finset.centroidWeights]
#align affine_basis.coord_apply_centroid AffineBasis.coord_apply_centroid

theorem card_eq_finrank_add_one [Fintype ι] (b : AffineBasis ι k P) :
    Fintype.card ι = FiniteDimensional.finrank k V + 1 :=
  haveI := b.finite_dimensional
  b.ind.affine_span_eq_top_iff_card_eq_finrank_add_one.mp b.tot
#align affine_basis.card_eq_finrank_add_one AffineBasis.card_eq_finrank_add_one

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (s «expr ⊆ » t) -/
theorem exists_affine_subbasis {t : Set P} (ht : affineSpan k t = ⊤) :
    ∃ (s : _)(_ : s ⊆ t)(b : AffineBasis (↥s) k P), b.points = coe := by
  obtain ⟨s, hst, h_tot, h_ind⟩ := exists_affine_independent k V t
  refine' ⟨s, hst, ⟨coe, h_ind, _⟩, rfl⟩
  rw [Subtype.range_coe, h_tot, ht]
#align affine_basis.exists_affine_subbasis AffineBasis.exists_affine_subbasis

variable (k V P)

theorem exists_affine_basis : ∃ (s : Set P)(b : AffineBasis (↥s) k P), b.points = coe :=
  let ⟨s, _, hs⟩ := exists_affine_subbasis (AffineSubspace.span_univ k V P)
  ⟨s, hs⟩
#align affine_basis.exists_affine_basis AffineBasis.exists_affine_basis

variable {k V P}

theorem exists_affine_basis_of_finite_dimensional [Fintype ι] [FiniteDimensional k V]
    (h : Fintype.card ι = FiniteDimensional.finrank k V + 1) : Nonempty (AffineBasis ι k P) := by
  obtain ⟨s, b, hb⟩ := AffineBasis.exists_affine_basis k V P
  lift s to Finset P using b.finite_set
  refine' ⟨b.comp_equiv <| Fintype.equivOfCardEq _⟩
  rw [h, ← b.card_eq_finrank_add_one]
#align
  affine_basis.exists_affine_basis_of_finite_dimensional AffineBasis.exists_affine_basis_of_finite_dimensional

end DivisionRing

end AffineBasis

