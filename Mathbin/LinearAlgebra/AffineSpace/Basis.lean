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


open_locale Affine BigOperators Matrix

open Set

universe u₁ u₂ u₃ u₄

/-- An affine basis is a family of affine-independent points whose span is the top subspace. -/
structure AffineBasis (ι : Type u₁) (k : Type u₂) {V : Type u₃} (P : Type u₄) [AddCommGroupₓ V] [affine_space V P]
  [Ringₓ k] [Module k V] where 
  points : ι → P 
  ind : AffineIndependent k points 
  tot : affineSpan k (range points) = ⊤

variable {ι : Type u₁} {k : Type u₂} {V : Type u₃} {P : Type u₄}

variable [AddCommGroupₓ V] [affine_space V P]

namespace AffineBasis

section Ringₓ

variable [Ringₓ k] [Module k V] (b : AffineBasis ι k P)

/-- The unique point in a single-point space is the simplest example of an affine basis. -/
instance : Inhabited (AffineBasis PUnit k PUnit) :=
  ⟨{ points := id, ind := affine_independent_of_subsingleton k id,
      tot :=
        by 
          simp  }⟩

/-- Given an affine basis for an affine space `P`, if we single out one member of the family, we
obtain a linear basis for the model space `V`.

The linear basis correpsonding to the singled-out member `i : ι` is indexed by `{j : ι // j ≠ i}`
and its `j`th element is `points j -ᵥ points i`. (See `basis_of_apply`.) -/
noncomputable def basis_of (i : ι) : Basis { j : ι // j ≠ i } k V :=
  Basis.mk ((affine_independent_iff_linear_independent_vsub k b.points i).mp b.ind)
    (by 
      suffices  :
        Submodule.span k (range fun j : { x // x ≠ i } => b.points («expr↑ » j) -ᵥ b.points i) =
          vectorSpan k (range b.points)
      ·
        rw [this, ←direction_affine_span, b.tot, AffineSubspace.direction_top]
      convRHS => rw [←image_univ]
      rw [vector_span_image_eq_span_vsub_set_right_ne k b.points (mem_univ i)]
      congr 
      ext v 
      simp )

@[simp]
theorem basis_of_apply (i : ι) (j : { j : ι // j ≠ i }) : b.basis_of i j = b.points («expr↑ » j) -ᵥ b.points i :=
  by 
    simp [basis_of]

/-- The `i`th barycentric coordinate of a point. -/
noncomputable def coord (i : ι) : P →ᵃ[k] k :=
  { toFun := fun q => 1 - (b.basis_of i).sumCoords (q -ᵥ b.points i), linear := -(b.basis_of i).sumCoords,
    map_vadd' :=
      fun q v =>
        by 
          rw [vadd_vsub_assoc, LinearMap.map_add, vadd_eq_add, LinearMap.neg_apply, sub_add_eq_sub_sub_swap, add_commₓ,
            sub_eq_add_neg] }

@[simp]
theorem coord_apply_eq (i : ι) : b.coord i (b.points i) = 1 :=
  by 
    simp only [coord, Basis.coe_sum_coords, LinearEquiv.map_zero, LinearEquiv.coe_coe, sub_zero, AffineMap.coe_mk,
      Finsupp.sum_zero_index, vsub_self]

@[simp]
theorem coord_apply_neq (i j : ι) (h : j ≠ i) : b.coord i (b.points j) = 0 :=
  by 
    rw [coord, AffineMap.coe_mk, ←Subtype.coe_mk j h, ←b.basis_of_apply i ⟨j, h⟩, Basis.sum_coords_self_apply, sub_self]

theorem coord_apply [DecidableEq ι] (i j : ι) : b.coord i (b.points j) = if i = j then 1 else 0 :=
  by 
    cases eq_or_ne i j <;> simp [h.symm]
    simp [h]

@[simp]
theorem coord_apply_combination_of_mem {s : Finset ι} {i : ι} (hi : i ∈ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b.points w) = w i :=
  by 
    classical 
    simp only [coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_true, mul_boole, hw,
      Function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b.points w hw]

@[simp]
theorem coord_apply_combination_of_not_mem {s : Finset ι} {i : ι} (hi : i ∉ s) {w : ι → k} (hw : s.sum w = 1) :
  b.coord i (s.affine_combination b.points w) = 0 :=
  by 
    classical 
    simp only [coord_apply, hi, Finset.affine_combination_eq_linear_combination, if_false, mul_boole, hw,
      Function.comp_app, smul_eq_mul, s.sum_ite_eq, s.map_affine_combination b.points w hw]

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem sum_coord_apply_eq_one [fintype ι] (q : P) : «expr = »(«expr∑ , »((i), b.coord i q), 1) :=
begin
  have [ident hq] [":", expr «expr ∈ »(q, affine_span k (range b.points))] [],
  { rw [expr b.tot] [],
    exact [expr affine_subspace.mem_top k V q] },
  obtain ["⟨", ident w, ",", ident hw, ",", ident rfl, "⟩", ":=", expr eq_affine_combination_of_mem_affine_span_of_fintype hq],
  convert [] [expr hw] [],
  ext [] [ident i] [],
  exact [expr b.coord_apply_combination_of_mem (finset.mem_univ i) hw]
end

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem affine_combination_coord_eq_self
[fintype ι]
(q : P) : «expr = »(finset.univ.affine_combination b.points (λ i, b.coord i q), q) :=
begin
  have [ident hq] [":", expr «expr ∈ »(q, affine_span k (range b.points))] [],
  { rw [expr b.tot] [],
    exact [expr affine_subspace.mem_top k V q] },
  obtain ["⟨", ident w, ",", ident hw, ",", ident rfl, "⟩", ":=", expr eq_affine_combination_of_mem_affine_span_of_fintype hq],
  congr,
  ext [] [ident i] [],
  exact [expr b.coord_apply_combination_of_mem (finset.mem_univ i) hw]
end

theorem ext_elem [Fintype ι] {q₁ q₂ : P} (h : ∀ i, b.coord i q₁ = b.coord i q₂) : q₁ = q₂ :=
  by 
    rw [←b.affine_combination_coord_eq_self q₁, ←b.affine_combination_coord_eq_self q₂]
    simp only [h]

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem coe_coord_of_subsingleton_eq_one [subsingleton ι] (i : ι) : «expr = »((b.coord i : P → k), 1) :=
begin
  ext [] [ident q] [],
  have [ident hp] [":", expr (range b.points).subsingleton] [],
  { rw ["<-", expr image_univ] [],
    apply [expr subsingleton.image],
    apply [expr subsingleton_of_subsingleton] },
  haveI [] [] [":=", expr affine_subspace.subsingleton_of_subsingleton_span_eq_top hp b.tot],
  let [ident s] [":", expr finset ι] [":=", expr {i}],
  have [ident hi] [":", expr «expr ∈ »(i, s)] [],
  { simp [] [] [] [] [] [] },
  have [ident hw] [":", expr «expr = »(s.sum (function.const ι (1 : k)), 1)] [],
  { simp [] [] [] [] [] [] },
  have [ident hq] [":", expr «expr = »(q, s.affine_combination b.points (function.const ι (1 : k)))] [],
  { simp [] [] [] [] [] [] },
  rw ["[", expr pi.one_apply, ",", expr hq, ",", expr b.coord_apply_combination_of_mem hi hw, "]"] []
end

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem surjective_coord [nontrivial ι] (i : ι) : «expr $ »(function.surjective, b.coord i) :=
begin
  classical,
  intros [ident x],
  obtain ["⟨", ident j, ",", ident hij, "⟩", ":=", expr exists_ne i],
  let [ident s] [":", expr finset ι] [":=", expr {i, j}],
  have [ident hi] [":", expr «expr ∈ »(i, s)] [],
  { simp [] [] [] [] [] [] },
  have [ident hj] [":", expr «expr ∈ »(j, s)] [],
  { simp [] [] [] [] [] [] },
  let [ident w] [":", expr ι → k] [":=", expr λ j', if «expr = »(j', i) then x else «expr - »(1, x)],
  have [ident hw] [":", expr «expr = »(s.sum w, 1)] [],
  { simp [] [] [] ["[", expr hij, ",", expr finset.sum_ite, ",", expr finset.filter_insert, ",", expr finset.filter_eq', "]"] [] [] },
  use [expr s.affine_combination b.points w],
  simp [] [] [] ["[", expr b.coord_apply_combination_of_mem hi hw, "]"] [] []
end

/-- The vector of barycentric coordinates of a given point with respect to an affine basis. -/
noncomputable def coords (q : P) (i : ι) :=
  b.coord i q

@[simp]
theorem coords_apply (q : P) (i : ι) : b.coords q i = b.coord i q :=
  rfl

/-- Given an affine basis `p`, and a family of points `q : ι' → P`, this is the matrix whose
rows are the barycentric coordinates of `q` with respect to `p`.

It is an affine equivalent of `basis.to_matrix`. -/
noncomputable def to_matrix {ι' : Type _} (q : ι' → P) : Matrix ι' ι k :=
  fun i j => b.coord j (q i)

@[simp]
theorem to_matrix_apply {ι' : Type _} (q : ι' → P) (i : ι') (j : ι) : b.to_matrix q i j = b.coord j (q i) :=
  rfl

@[simp]
theorem to_matrix_self [DecidableEq ι] : b.to_matrix b.points = (1 : Matrix ι ι k) :=
  by 
    ext i j 
    rw [to_matrix_apply, coord_apply, Matrix.one_eq_pi_single, Pi.single_apply]

variable {ι' : Type _} [Fintype ι'] [Fintype ι] (b₂ : AffineBasis ι k P)

theorem to_matrix_row_sum_one {ι' : Type _} (q : ι' → P) (i : ι') : (∑j, b.to_matrix q i j) = 1 :=
  by 
    simp 

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a right inverse, then `p` is affine independent. -/
theorem affine_independent_of_to_matrix_right_inv
[decidable_eq ι']
(p : ι' → P)
{A : matrix ι ι' k}
(hA : «expr = »(«expr ⬝ »(b.to_matrix p, A), 1)) : affine_independent k p :=
begin
  rw [expr affine_independent_iff_eq_of_fintype_affine_combination_eq] [],
  intros [ident w₁, ident w₂, ident hw₁, ident hw₂, ident hweq],
  have [ident hweq'] [":", expr «expr = »((b.to_matrix p).vec_mul w₁, (b.to_matrix p).vec_mul w₂)] [],
  { ext [] [ident j] [],
    change [expr «expr = »(«expr∑ , »((i), «expr • »(w₁ i, b.coord j (p i))), «expr∑ , »((i), «expr • »(w₂ i, b.coord j (p i))))] [] [],
    rw ["[", "<-", expr finset.univ.affine_combination_eq_linear_combination _ _ hw₁, ",", "<-", expr finset.univ.affine_combination_eq_linear_combination _ _ hw₂, ",", "<-", expr finset.univ.map_affine_combination p w₁ hw₁, ",", "<-", expr finset.univ.map_affine_combination p w₂ hw₂, ",", expr hweq, "]"] [] },
  replace [ident hweq'] [] [":=", expr congr_arg (λ w, A.vec_mul w) hweq'],
  simpa [] [] ["only"] ["[", expr matrix.vec_mul_vec_mul, ",", "<-", expr matrix.mul_eq_mul, ",", expr hA, ",", expr matrix.vec_mul_one, "]"] [] ["using", expr hweq']
end

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a family of points `p : ι' → P` and an affine basis `b`, if the matrix whose rows are the
coordinates of `p` with respect `b` has a left inverse, then `p` spans the the entire space. -/
theorem affine_span_eq_top_of_to_matrix_left_inv
[decidable_eq ι]
[nontrivial k]
(p : ι' → P)
{A : matrix ι ι' k}
(hA : «expr = »(«expr ⬝ »(A, b.to_matrix p), 1)) : «expr = »(affine_span k (range p), «expr⊤»()) :=
begin
  suffices [] [":", expr ∀ i, «expr ∈ »(b.points i, affine_span k (range p))],
  { rw ["[", expr eq_top_iff, ",", "<-", expr b.tot, ",", expr affine_span_le, "]"] [],
    rintros [ident q, "⟨", ident i, ",", ident rfl, "⟩"],
    exact [expr this i] },
  intros [ident i],
  have [ident hAi] [":", expr «expr = »(«expr∑ , »((j), A i j), 1)] [],
  { calc
      «expr = »(«expr∑ , »((j), A i j), «expr∑ , »((j), «expr * »(A i j, «expr∑ , »((l), b.to_matrix p j l)))) : by simp [] [] [] [] [] []
      «expr = »(..., «expr∑ , »((j), «expr∑ , »((l), «expr * »(A i j, b.to_matrix p j l)))) : by simp_rw [expr finset.mul_sum] []
      «expr = »(..., «expr∑ , »((l), «expr∑ , »((j), «expr * »(A i j, b.to_matrix p j l)))) : by rw [expr finset.sum_comm] []
      «expr = »(..., «expr∑ , »((l), «expr ⬝ »(A, b.to_matrix p) i l)) : rfl
      «expr = »(..., 1) : by simp [] [] [] ["[", expr hA, ",", expr matrix.one_apply, ",", expr finset.filter_eq, "]"] [] [] },
  have [ident hbi] [":", expr «expr = »(b.points i, finset.univ.affine_combination p (A i))] [],
  { apply [expr b.ext_elem],
    intros [ident j],
    rw ["[", expr b.coord_apply, ",", expr finset.univ.map_affine_combination _ _ hAi, ",", expr finset.univ.affine_combination_eq_linear_combination _ _ hAi, "]"] [],
    change [expr «expr = »(_, «expr ⬝ »(A, b.to_matrix p) i j)] [] [],
    simp_rw ["[", expr hA, ",", expr matrix.one_apply, ",", expr @eq_comm _ i j, "]"] [],
    congr },
  rw [expr hbi] [],
  exact [expr affine_combination_mem_affine_span hAi p]
end

/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_inv_mul_affine_basis_to_matrix`. -/
@[simp]
theorem to_matrix_vec_mul_coords (x : P) : (b.to_matrix b₂.points).vecMul (b₂.coords x) = b.coords x :=
  by 
    ext j 
    change _ = b.coord j x 
    convRHS => rw [←b₂.affine_combination_coord_eq_self x]
    rw [Finset.map_affine_combination _ _ _ (b₂.sum_coord_apply_eq_one x)]
    simp [Matrix.vecMulₓ, Matrix.dotProduct, to_matrix_apply, coords]

variable [DecidableEq ι]

theorem to_matrix_mul_to_matrix : b.to_matrix b₂.points ⬝ b₂.to_matrix b.points = 1 :=
  by 
    ext l m 
    change (b₂.to_matrix b.points).vecMul (b.coords (b₂.points l)) m = _ 
    rw [to_matrix_vec_mul_coords, coords_apply, ←to_matrix_apply, to_matrix_self]

theorem is_unit_to_matrix : IsUnit (b.to_matrix b₂.points) :=
  ⟨{ val := b.to_matrix b₂.points, inv := b₂.to_matrix b.points, val_inv := b.to_matrix_mul_to_matrix b₂,
      inv_val := b₂.to_matrix_mul_to_matrix b },
    rfl⟩

theorem is_unit_to_matrix_iff [Nontrivial k] (p : ι → P) :
  IsUnit (b.to_matrix p) ↔ AffineIndependent k p ∧ affineSpan k (range p) = ⊤ :=
  by 
    split 
    ·
      rintro ⟨⟨B, A, hA, hA'⟩, rfl : B = b.to_matrix p⟩
      rw [Matrix.mul_eq_mul] at hA hA' 
      exact ⟨b.affine_independent_of_to_matrix_right_inv p hA, b.affine_span_eq_top_of_to_matrix_left_inv p hA'⟩
    ·
      rintro ⟨h_tot, h_ind⟩
      let b' : AffineBasis ι k P := ⟨p, h_tot, h_ind⟩
      change IsUnit (b.to_matrix b'.points)
      exact b.is_unit_to_matrix b'

end Ringₓ

section CommRingₓ

variable [CommRingₓ k] [Module k V] [DecidableEq ι] [Fintype ι]

variable (b b₂ : AffineBasis ι k P)

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A change of basis formula for barycentric coordinates.

See also `affine_basis.to_matrix_vec_mul_coords`. -/
@[simp]
theorem to_matrix_inv_vec_mul_to_matrix
(x : P) : «expr = »(«expr ⁻¹»(b.to_matrix b₂.points).vec_mul (b.coords x), b₂.coords x) :=
begin
  have [ident hu] [] [":=", expr b.is_unit_to_matrix b₂],
  rw [expr matrix.is_unit_iff_is_unit_det] ["at", ident hu],
  rw ["[", "<-", expr b.to_matrix_vec_mul_coords b₂, ",", expr matrix.vec_mul_vec_mul, ",", expr matrix.mul_nonsing_inv _ hu, ",", expr matrix.vec_mul_one, "]"] []
end

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If we fix a background affine basis `b`, then for any other basis `b₂`, we can characterise
the barycentric coordinates provided by `b₂` in terms of determinants relative to `b`. -/
theorem det_smul_coords_eq_cramer_coords
(x : P) : «expr = »(«expr • »((b.to_matrix b₂.points).det, b₂.coords x), «expr ᵀ»(b.to_matrix b₂.points).cramer (b.coords x)) :=
begin
  have [ident hu] [] [":=", expr b.is_unit_to_matrix b₂],
  rw [expr matrix.is_unit_iff_is_unit_det] ["at", ident hu],
  rw ["[", "<-", expr b.to_matrix_inv_vec_mul_to_matrix, ",", expr matrix.det_smul_inv_vec_mul_eq_cramer_transpose _ _ hu, "]"] []
end

end CommRingₓ

section Field

variable [Field k] [Module k V]

include V

variable (k V P)

theorem exists_affine_basis : ∃ s : Set P, Nonempty (AffineBasis («expr↥ » s) k P) :=
  by 
    obtain ⟨s, -, h_tot, h_ind⟩ := exists_affine_independent k V (Set.Univ : Set P)
    refine' ⟨s, ⟨⟨(coeₓ : s → P), h_ind, _⟩⟩⟩
    rw [Subtype.range_coe, h_tot, AffineSubspace.span_univ]

variable {k V P}

-- error in LinearAlgebra.AffineSpace.Basis: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_affine_basis_of_finite_dimensional
{ι : Type*}
[fintype ι]
[finite_dimensional k V]
(h : «expr = »(fintype.card ι, «expr + »(finite_dimensional.finrank k V, 1))) : nonempty (affine_basis ι k P) :=
begin
  obtain ["⟨", ident s, ",", "⟨", "⟨", ident incl, ",", ident h_ind, ",", ident h_tot, "⟩", "⟩", "⟩", ":=", expr affine_basis.exists_affine_basis k V P],
  haveI [] [":", expr fintype s] [":=", expr fintype_of_fin_dim_affine_independent k h_ind],
  have [ident hs] [":", expr «expr = »(fintype.card ι, fintype.card s)] [],
  { rw [expr h] [],
    exact [expr (h_ind.affine_span_eq_top_iff_card_eq_finrank_add_one.mp h_tot).symm] },
  rw ["<-", expr affine_independent_equiv (fintype.equiv_of_card_eq hs)] ["at", ident h_ind],
  refine [expr ⟨⟨_, h_ind, _⟩⟩],
  rw [expr range_comp] [],
  simp [] [] [] ["[", expr h_tot, "]"] [] []
end

end Field

end AffineBasis

