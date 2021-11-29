import Mathbin.Algebra.Regular.Smul 
import Mathbin.LinearAlgebra.Matrix.Adjugate 
import Mathbin.LinearAlgebra.Matrix.Polynomial

/-!
# Nonsingular inverses

In this file, we define an inverse for square matrices of invertible determinant.

For matrices that are not square or not of full rank, there is a more general notion of
pseudoinverses which we do not consider here.

The definition of inverse used in this file is the adjugate divided by the determinant.
We show that dividing the adjugate by `det A` (if possible), giving a matrix `A⁻¹` (`nonsing_inv`),
will result in a multiplicative inverse to `A`.

Note that there are at least three different inverses in mathlib:

* `A⁻¹` (`has_inv.inv`): alone, this satisfies no properties, although it is usually used in
  conjunction with `group` or `group_with_zero`. On matrices, this is defined to be zero when no
  inverse exists.
* `⅟A` (`inv_of`): this is only available in the presence of `[invertible A]`, which guarantees an
  inverse exists.
* `ring.inverse A`: this is defined on any `monoid_with_zero`, and just like `⁻¹` on matrices, is
  defined to be zero when no inverse exists.

We start by working with `invertible`, and show the main results:

* `matrix.invertible_of_det_invertible`
* `matrix.det_invertible_of_invertible`
* `matrix.is_unit_iff_is_unit_det`
* `matrix.mul_eq_one_comm`

After this we define `matrix.has_inv` and show it matches `⅟A` and `ring.inverse A`.
The rest of the results in the file are then about `A⁻¹`

## References

  * https://en.wikipedia.org/wiki/Cramer's_rule#Finding_inverse_matrix

## Tags

matrix inverse, cramer, cramer's rule, adjugate
-/


namespace Matrix

universe u v

variable {n : Type u} [DecidableEq n] [Fintype n] {α : Type v} [CommRingₓ α]

open_locale Matrix BigOperators

open Equiv Equiv.Perm Finset

variable (A : Matrix n n α) (B : Matrix n n α)

/-! ### Matrices are `invertible` iff their determinants are -/


section Invertible

/-- A copy of `inv_of_mul_self` using `⬝` not `*`. -/
protected theorem inv_of_mul_self [Invertible A] : ⅟ A ⬝ A = 1 :=
  inv_of_mul_self A

/-- A copy of `mul_inv_of_self` using `⬝` not `*`. -/
protected theorem mul_inv_of_self [Invertible A] : A ⬝ ⅟ A = 1 :=
  mul_inv_of_self A

/-- If `A.det` has a constructive inverse, produce one for `A`. -/
def invertible_of_det_invertible [Invertible A.det] : Invertible A :=
  { invOf := ⅟ A.det • A.adjugate,
    mul_inv_of_self :=
      by 
        rw [mul_smul_comm, Matrix.mul_eq_mul, mul_adjugate, smul_smul, inv_of_mul_self, one_smul],
    inv_of_mul_self :=
      by 
        rw [smul_mul_assoc, Matrix.mul_eq_mul, adjugate_mul, smul_smul, inv_of_mul_self, one_smul] }

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem inv_of_eq [invertible A.det] [invertible A] : «expr = »(«expr⅟»() A, «expr • »(«expr⅟»() A.det, A.adjugate)) :=
by { letI [] [] [":=", expr invertible_of_det_invertible A],
  convert [] [expr (rfl : «expr = »(«expr⅟»() A, _))] [] }

/-- `A.det` is invertible if `A` has a left inverse. -/
def det_invertible_of_left_inverse (h : B ⬝ A = 1) : Invertible A.det :=
  { invOf := B.det,
    mul_inv_of_self :=
      by 
        rw [mul_commₓ, ←det_mul, h, det_one],
    inv_of_mul_self :=
      by 
        rw [←det_mul, h, det_one] }

/-- `A.det` is invertible if `A` has a right inverse. -/
def det_invertible_of_right_inverse (h : A ⬝ B = 1) : Invertible A.det :=
  { invOf := B.det,
    mul_inv_of_self :=
      by 
        rw [←det_mul, h, det_one],
    inv_of_mul_self :=
      by 
        rw [mul_commₓ, ←det_mul, h, det_one] }

/-- If `A` has a constructive inverse, produce one for `A.det`. -/
def det_invertible_of_invertible [Invertible A] : Invertible A.det :=
  det_invertible_of_left_inverse A (⅟ A) (inv_of_mul_self _)

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem det_inv_of [invertible A] [invertible A.det] : «expr = »((«expr⅟»() A).det, «expr⅟»() A.det) :=
by { letI [] [] [":=", expr det_invertible_of_invertible A],
  convert [] [expr (rfl : «expr = »(_, «expr⅟»() A.det))] [] }

/-- Together `matrix.det_invertible_of_invertible` and `matrix.invertible_of_det_invertible` form an
equivalence, although both sides of the equiv are subsingleton anyway. -/
@[simps]
def invertible_equiv_det_invertible : Invertible A ≃ Invertible A.det :=
  { toFun := @det_invertible_of_invertible _ _ _ _ _ A, invFun := @invertible_of_det_invertible _ _ _ _ _ A,
    left_inv := fun _ => Subsingleton.elimₓ _ _, right_inv := fun _ => Subsingleton.elimₓ _ _ }

variable {A B}

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_eq_one_comm : «expr ↔ »(«expr = »(«expr ⬝ »(A, B), 1), «expr = »(«expr ⬝ »(B, A), 1)) :=
suffices ∀ A B, «expr = »(«expr ⬝ »(A, B), 1) → «expr = »(«expr ⬝ »(B, A), 1), from ⟨this A B, this B A⟩,
assume A B h, begin
  letI [] [":", expr invertible B.det] [":=", expr det_invertible_of_left_inverse _ _ h],
  letI [] [":", expr invertible B] [":=", expr invertible_of_det_invertible B],
  calc
    «expr = »(«expr ⬝ »(B, A), «expr ⬝ »(«expr ⬝ »(B, A), «expr ⬝ »(B, «expr⅟»() B))) : by rw ["[", expr matrix.mul_inv_of_self, ",", expr matrix.mul_one, "]"] []
    «expr = »(..., «expr ⬝ »(B, «expr ⬝ »(«expr ⬝ »(A, B), «expr⅟»() B))) : by simp [] [] ["only"] ["[", expr matrix.mul_assoc, "]"] [] []
    «expr = »(..., «expr ⬝ »(B, «expr⅟»() B)) : by rw ["[", expr h, ",", expr matrix.one_mul, "]"] []
    «expr = »(..., 1) : matrix.mul_inv_of_self B
end

variable (A B)

/-- We can construct an instance of invertible A if A has a left inverse. -/
def invertible_of_left_inverse (h : B ⬝ A = 1) : Invertible A :=
  ⟨B, h, mul_eq_one_comm.mp h⟩

/-- We can construct an instance of invertible A if A has a right inverse. -/
def invertible_of_right_inverse (h : A ⬝ B = 1) : Invertible A :=
  ⟨B, mul_eq_one_comm.mp h, h⟩

/-- Given a proof that `A.det` has a constructive inverse, lift `A` to `units (matrix n n α)`-/
def unit_of_det_invertible [Invertible A.det] : Units (Matrix n n α) :=
  @unitOfInvertible _ _ A (invertible_of_det_invertible A)

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- When lowered to a prop, `matrix.invertible_equiv_det_invertible` forms an `iff`. -/
theorem is_unit_iff_is_unit_det : «expr ↔ »(is_unit A, is_unit A.det) :=
begin
  split; rintros ["⟨", ident x, ",", ident hx, "⟩"]; refine [expr @is_unit_of_invertible _ _ _ (id _)],
  { haveI [] [":", expr invertible A] [":=", expr hx.rec x.invertible],
    apply [expr det_invertible_of_invertible] },
  { haveI [] [":", expr invertible A.det] [":=", expr hx.rec x.invertible],
    apply [expr invertible_of_det_invertible] }
end

/-! #### Variants of the statements above with `is_unit`-/


theorem is_unit_det_of_invertible [Invertible A] : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (det_invertible_of_invertible A)

variable {A B}

theorem is_unit_det_of_left_inverse (h : B ⬝ A = 1) : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (det_invertible_of_left_inverse _ _ h)

theorem is_unit_det_of_right_inverse (h : A ⬝ B = 1) : IsUnit A.det :=
  @is_unit_of_invertible _ _ _ (det_invertible_of_right_inverse _ _ h)

theorem det_ne_zero_of_left_inverse [Nontrivial α] (h : B ⬝ A = 1) : A.det ≠ 0 :=
  (is_unit_det_of_left_inverse h).ne_zero

theorem det_ne_zero_of_right_inverse [Nontrivial α] (h : A ⬝ B = 1) : A.det ≠ 0 :=
  (is_unit_det_of_right_inverse h).ne_zero

end Invertible

open_locale Classical

theorem is_unit_det_transpose (h : IsUnit A.det) : IsUnit (A)ᵀ.det :=
  by 
    rw [det_transpose]
    exact h

/-! ### A noncomputable `has_inv` instance  -/


/-- The inverse of a square matrix, when it is invertible (and zero otherwise).-/
noncomputable instance : HasInv (Matrix n n α) :=
  ⟨fun A => Ring.inverse A.det • A.adjugate⟩

theorem inv_def (A : Matrix n n α) : A⁻¹ = Ring.inverse A.det • A.adjugate :=
  rfl

theorem nonsing_inv_apply_not_is_unit (h : ¬IsUnit A.det) : A⁻¹ = 0 :=
  by 
    rw [inv_def, Ring.inverse_non_unit _ h, zero_smul]

theorem nonsing_inv_apply (h : IsUnit A.det) : A⁻¹ = («expr↑ » (h.unit⁻¹) : α) • A.adjugate :=
  by 
    rw [inv_def, ←Ring.inverse_unit h.unit, IsUnit.unit_spec]

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The nonsingular inverse is the same as `inv_of` when `A` is invertible. -/
@[simp]
theorem inv_of_eq_nonsing_inv [invertible A] : «expr = »(«expr⅟»() A, «expr ⁻¹»(A)) :=
begin
  letI [] [] [":=", expr det_invertible_of_invertible A],
  rw ["[", expr inv_def, ",", expr ring.inverse_invertible, ",", expr inv_of_eq, "]"] []
end

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The nonsingular inverse is the same as the general `ring.inverse`. -/
theorem nonsing_inv_eq_ring_inverse : «expr = »(«expr ⁻¹»(A), ring.inverse A) :=
begin
  by_cases [expr h_det, ":", expr is_unit A.det],
  { casesI [expr (A.is_unit_iff_is_unit_det.mpr h_det).nonempty_invertible] [],
    rw ["[", "<-", expr inv_of_eq_nonsing_inv, ",", expr ring.inverse_invertible, "]"] [] },
  { have [ident h] [] [":=", expr mt A.is_unit_iff_is_unit_det.mp h_det],
    rw ["[", expr ring.inverse_non_unit _ h, ",", expr nonsing_inv_apply_not_is_unit A h_det, "]"] [] }
end

theorem transpose_nonsing_inv : (A⁻¹)ᵀ = (A)ᵀ⁻¹ :=
  by 
    rw [inv_def, inv_def, transpose_smul, det_transpose, adjugate_transpose]

theorem conj_transpose_nonsing_inv [StarRing α] : (A⁻¹)ᴴ = (A)ᴴ⁻¹ :=
  by 
    rw [inv_def, inv_def, conj_transpose_smul, det_conj_transpose, adjugate_conj_transpose, Ringₓ.inverse_star]

/-- The `nonsing_inv` of `A` is a right inverse. -/
@[simp]
theorem mul_nonsing_inv (h : IsUnit A.det) : A ⬝ A⁻¹ = 1 :=
  by 
    cases' (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible 
    rw [←inv_of_eq_nonsing_inv, Matrix.mul_inv_of_self]

/-- The `nonsing_inv` of `A` is a left inverse. -/
@[simp]
theorem nonsing_inv_mul (h : IsUnit A.det) : A⁻¹ ⬝ A = 1 :=
  by 
    cases' (A.is_unit_iff_is_unit_det.mpr h).nonempty_invertible 
    rw [←inv_of_eq_nonsing_inv, Matrix.inv_of_mul_self]

@[simp]
theorem mul_inv_of_invertible [Invertible A] : A ⬝ A⁻¹ = 1 :=
  mul_nonsing_inv A (is_unit_det_of_invertible A)

@[simp]
theorem inv_mul_of_invertible [Invertible A] : A⁻¹ ⬝ A = 1 :=
  nonsing_inv_mul A (is_unit_det_of_invertible A)

theorem nonsing_inv_cancel_or_zero : A⁻¹ ⬝ A = 1 ∧ A ⬝ A⁻¹ = 1 ∨ A⁻¹ = 0 :=
  by 
    byCases' h : IsUnit A.det
    ·
      exact Or.inl ⟨nonsing_inv_mul _ h, mul_nonsing_inv _ h⟩
    ·
      exact Or.inr (nonsing_inv_apply_not_is_unit _ h)

theorem det_nonsing_inv_mul_det (h : IsUnit A.det) : (A⁻¹.det*A.det) = 1 :=
  by 
    rw [←det_mul, A.nonsing_inv_mul h, det_one]

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem det_nonsing_inv : «expr = »(«expr ⁻¹»(A).det, ring.inverse A.det) :=
begin
  by_cases [expr h, ":", expr is_unit A.det],
  { casesI [expr h.nonempty_invertible] [],
    letI [] [] [":=", expr invertible_of_det_invertible A],
    rw ["[", expr ring.inverse_invertible, ",", "<-", expr inv_of_eq_nonsing_inv, ",", expr det_inv_of, "]"] [] },
  casesI [expr is_empty_or_nonempty n] [],
  { rw ["[", expr det_is_empty, ",", expr det_is_empty, ",", expr ring.inverse_one, "]"] [] },
  { rw ["[", expr ring.inverse_non_unit _ h, ",", expr nonsing_inv_apply_not_is_unit _ h, ",", expr det_zero «expr‹ ›»(_), "]"] [] }
end

theorem is_unit_nonsing_inv_det (h : IsUnit A.det) : IsUnit A⁻¹.det :=
  is_unit_of_mul_eq_one _ _ (A.det_nonsing_inv_mul_det h)

@[simp]
theorem nonsing_inv_nonsing_inv (h : IsUnit A.det) : A⁻¹⁻¹ = A :=
  calc A⁻¹⁻¹ = 1 ⬝ A⁻¹⁻¹ :=
    by 
      rw [Matrix.one_mul]
    _ = A ⬝ A⁻¹ ⬝ A⁻¹⁻¹ :=
    by 
      rw [A.mul_nonsing_inv h]
    _ = A :=
    by 
      rw [Matrix.mul_assoc, A⁻¹.mul_nonsing_inv (A.is_unit_nonsing_inv_det h), Matrix.mul_one]
    

theorem is_unit_nonsing_inv_det_iff {A : Matrix n n α} : IsUnit A⁻¹.det ↔ IsUnit A.det :=
  by 
    rw [Matrix.det_nonsing_inv, is_unit_ring_inverse]

/-- A version of `matrix.invertible_of_det_invertible` with the inverse defeq to `A⁻¹` that is
therefore noncomputable. -/
noncomputable def invertible_of_is_unit_det (h : IsUnit A.det) : Invertible A :=
  ⟨A⁻¹, nonsing_inv_mul A h, mul_nonsing_inv A h⟩

/-- A version of `matrix.units_of_det_invertible` with the inverse defeq to `A⁻¹` that is therefore
noncomputable. -/
noncomputable def nonsing_inv_unit (h : IsUnit A.det) : Units (Matrix n n α) :=
  @unitOfInvertible _ _ _ (invertible_of_is_unit_det A h)

theorem unit_of_det_invertible_eq_nonsing_inv_unit [Invertible A.det] :
  unit_of_det_invertible A = nonsing_inv_unit A (is_unit_of_invertible _) :=
  by 
    ext 
    rfl

variable {A} {B}

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If matrix A is left invertible, then its inverse equals its left inverse. -/
theorem inv_eq_left_inv (h : «expr = »(«expr ⬝ »(B, A), 1)) : «expr = »(«expr ⁻¹»(A), B) :=
begin
  letI [] [] [":=", expr invertible_of_left_inverse _ _ h],
  exact [expr «expr ▸ »(inv_of_eq_nonsing_inv A, inv_of_eq_left_inv h)]
end

/-- If matrix A is right invertible, then its inverse equals its right inverse. -/
theorem inv_eq_right_inv (h : A ⬝ B = 1) : A⁻¹ = B :=
  inv_eq_left_inv (mul_eq_one_comm.2 h)

section InvEqInv

variable {C : Matrix n n α}

/-- The left inverse of matrix A is unique when existing. -/
theorem left_inv_eq_left_inv (h : B ⬝ A = 1) (g : C ⬝ A = 1) : B = C :=
  by 
    rw [←inv_eq_left_inv h, ←inv_eq_left_inv g]

/-- The right inverse of matrix A is unique when existing. -/
theorem right_inv_eq_right_inv (h : A ⬝ B = 1) (g : A ⬝ C = 1) : B = C :=
  by 
    rw [←inv_eq_right_inv h, ←inv_eq_right_inv g]

/-- The right inverse of matrix A equals the left inverse of A when they exist. -/
theorem right_inv_eq_left_inv (h : A ⬝ B = 1) (g : C ⬝ A = 1) : B = C :=
  by 
    rw [←inv_eq_right_inv h, ←inv_eq_left_inv g]

theorem inv_inj (h : A⁻¹ = B⁻¹) (h' : IsUnit A.det) : A = B :=
  by 
    refine' left_inv_eq_left_inv (mul_nonsing_inv _ h') _ 
    rw [h]
    refine' mul_nonsing_inv _ _ 
    rwa [←is_unit_nonsing_inv_det_iff, ←h, is_unit_nonsing_inv_det_iff]

end InvEqInv

variable (A)

-- error in LinearAlgebra.Matrix.NonsingularInverse: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem inv_zero : «expr = »(«expr ⁻¹»((0 : matrix n n α)), 0) :=
begin
  casesI [expr subsingleton_or_nontrivial α] ["with", ident ht, ident ht],
  { simp [] [] [] [] [] [] },
  cases [expr (fintype.card n).zero_le.eq_or_lt] ["with", ident hc, ident hc],
  { rw ["[", expr eq_comm, ",", expr fintype.card_eq_zero_iff, "]"] ["at", ident hc],
    haveI [] [] [":=", expr hc],
    ext [] [ident i] [],
    exact [expr (is_empty.false i).elim] },
  { have [ident hn] [":", expr nonempty n] [":=", expr fintype.card_pos_iff.mp hc],
    refine [expr nonsing_inv_apply_not_is_unit _ _],
    simp [] [] [] ["[", expr hn, "]"] [] [] }
end

@[simp]
theorem inv_one : (1 : Matrix n n α)⁻¹ = 1 :=
  inv_eq_left_inv
    (by 
      simp )

theorem inv_smul (k : α) [Invertible k] (h : IsUnit A.det) : (k • A)⁻¹ = ⅟ k • A⁻¹ :=
  inv_eq_left_inv
    (by 
      simp [h, smul_smul])

theorem inv_smul' (k : Units α) (h : IsUnit A.det) : (k • A)⁻¹ = k⁻¹ • A⁻¹ :=
  inv_eq_left_inv
    (by 
      simp [h, smul_smul])

theorem inv_adjugate (A : Matrix n n α) (h : IsUnit A.det) : adjugate A⁻¹ = h.unit⁻¹ • A :=
  by 
    refine' inv_eq_left_inv _ 
    rw [smul_mul, mul_adjugate, Units.smul_def, smul_smul, h.coe_inv_mul, one_smul]

@[simp]
theorem inv_inv_inv (A : Matrix n n α) : A⁻¹⁻¹⁻¹ = A⁻¹ :=
  by 
    byCases' h : IsUnit A.det
    ·
      rw [nonsing_inv_nonsing_inv _ h]
    ·
      simp [nonsing_inv_apply_not_is_unit _ h]

theorem mul_inv_rev (A B : Matrix n n α) : (A ⬝ B)⁻¹ = B⁻¹ ⬝ A⁻¹ :=
  by 
    simp only [inv_def]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, det_mul, adjugate_mul_distrib, Ring.mul_inverse_rev]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_mul_vec_eq_cramer (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
  A.det • A⁻¹.mulVec b = cramer A b :=
  by 
    rw [cramer_eq_adjugate_mul_vec, A.nonsing_inv_apply h, ←smul_mul_vec_assoc, smul_smul, h.mul_coe_inv, one_smul]

/-- One form of **Cramer's rule**. See `matrix.mul_vec_cramer` for a stronger form. -/
@[simp]
theorem det_smul_inv_vec_mul_eq_cramer_transpose (A : Matrix n n α) (b : n → α) (h : IsUnit A.det) :
  A.det • A⁻¹.vecMul b = cramer (A)ᵀ b :=
  by 
    rw [←A⁻¹.transpose_transpose, vec_mul_transpose, transpose_nonsing_inv, ←det_transpose,
      (A)ᵀ.det_smul_inv_mul_vec_eq_cramer _ (is_unit_det_transpose A h)]

end Matrix

