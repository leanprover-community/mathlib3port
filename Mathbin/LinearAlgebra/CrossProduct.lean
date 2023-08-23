/-
Copyright (c) 2021 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak, Kyle Miller, Eric Wieser
-/
import Mathbin.Data.Matrix.Notation
import Mathbin.LinearAlgebra.BilinearMap
import Mathbin.LinearAlgebra.Matrix.Determinant
import Mathbin.Algebra.Lie.Basic

#align_import linear_algebra.cross_product from "leanprover-community/mathlib"@"1b0a28e1c93409dbf6d69526863cd9984ef652ce"

/-!
# Cross products

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines the cross product of vectors in $R^3$ for $R$ a commutative ring,
as a bilinear map.

## Main definitions

* `cross_product` is the cross product of pairs of vectors in $R^3$.

## Main results

* `triple_product_eq_det`
* `cross_dot_cross`
* `jacobi_cross`

## Notation

The locale `matrix` gives the following notation:

* `×₃` for the cross product

## Tags

crossproduct
-/


open Matrix

open scoped Matrix

variable {R : Type _} [CommRing R]

#print crossProduct /-
/-- The cross product of two vectors in $R^3$ for $R$ a commutative ring. -/
def crossProduct : (Fin 3 → R) →ₗ[R] (Fin 3 → R) →ₗ[R] Fin 3 → R :=
  by
  apply
    LinearMap.mk₂ R fun a b : Fin 3 → R =>
      ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]
  · intros
    simp [vec3_add (_ : R), add_comm, add_assoc, add_left_comm, add_mul, sub_eq_add_neg]
  · intros
    simp [smul_vec3 (_ : R) (_ : R), mul_comm, mul_assoc, mul_left_comm, mul_add, sub_eq_add_neg]
  · intros
    simp [vec3_add (_ : R), add_comm, add_assoc, add_left_comm, mul_add, sub_eq_add_neg]
  · intros
    simp [smul_vec3 (_ : R) (_ : R), mul_comm, mul_assoc, mul_left_comm, mul_add, sub_eq_add_neg]
#align cross_product crossProduct
-/

scoped[Matrix] infixl:74 " ×₃ " => crossProduct

#print cross_apply /-
theorem cross_apply (a b : Fin 3 → R) :
    a ×₃ b = ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0] :=
  rfl
#align cross_apply cross_apply
-/

section ProductsProperties

#print cross_anticomm /-
@[simp]
theorem cross_anticomm (v w : Fin 3 → R) : -(v ×₃ w) = w ×₃ v := by simp [cross_apply, mul_comm]
#align cross_anticomm cross_anticomm
-/

alias neg_cross := cross_anticomm
#align neg_cross neg_cross

#print cross_anticomm' /-
@[simp]
theorem cross_anticomm' (v w : Fin 3 → R) : v ×₃ w + w ×₃ v = 0 := by
  rw [add_eq_zero_iff_eq_neg, cross_anticomm]
#align cross_anticomm' cross_anticomm'
-/

#print cross_self /-
@[simp]
theorem cross_self (v : Fin 3 → R) : v ×₃ v = 0 := by simp [cross_apply, mul_comm]
#align cross_self cross_self
-/

#print dot_self_cross /-
/-- The cross product of two vectors is perpendicular to the first vector. -/
@[simp]
theorem dot_self_cross (v w : Fin 3 → R) : v ⬝ᵥ v ×₃ w = 0 := by
  simp [cross_apply, vec3_dot_product, mul_sub, mul_assoc, mul_left_comm]
#align dot_self_cross dot_self_cross
-/

#print dot_cross_self /-
/-- The cross product of two vectors is perpendicular to the second vector. -/
@[simp]
theorem dot_cross_self (v w : Fin 3 → R) : w ⬝ᵥ v ×₃ w = 0 := by
  rw [← cross_anticomm, Matrix.dotProduct_neg, dot_self_cross, neg_zero]
#align dot_cross_self dot_cross_self
-/

#print triple_product_permutation /-
/-- Cyclic permutations preserve the triple product. See also `triple_product_eq_det`. -/
theorem triple_product_permutation (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = v ⬝ᵥ w ×₃ u :=
  by
  simp only [cross_apply, vec3_dot_product, Matrix.head_cons, Matrix.cons_vec_bit0_eq_alt0,
    Matrix.empty_vecAppend, Matrix.cons_val_one, Matrix.cons_vecAlt0, Matrix.cons_vecAppend,
    Matrix.cons_val_zero]
  ring
#align triple_product_permutation triple_product_permutation
-/

#print triple_product_eq_det /-
/-- The triple product of `u`, `v`, and `w` is equal to the determinant of the matrix
    with those vectors as its rows. -/
theorem triple_product_eq_det (u v w : Fin 3 → R) : u ⬝ᵥ v ×₃ w = Matrix.det ![u, v, w] :=
  by
  simp only [vec3_dot_product, cross_apply, Matrix.det_fin_three, Matrix.head_cons,
    Matrix.cons_vec_bit0_eq_alt0, Matrix.empty_vecAlt0, Matrix.cons_vecAlt0, Matrix.vecHead_vecAlt0,
    Matrix.vecAppend_apply_zero, Matrix.empty_vecAppend, Matrix.cons_vecAppend, Matrix.cons_val',
    Matrix.cons_val_one, Matrix.cons_val_zero]
  ring
#align triple_product_eq_det triple_product_eq_det
-/

#print cross_dot_cross /-
/-- The scalar quadruple product identity, related to the Binet-Cauchy identity. -/
theorem cross_dot_cross (u v w x : Fin 3 → R) :
    u ×₃ v ⬝ᵥ w ×₃ x = u ⬝ᵥ w * v ⬝ᵥ x - u ⬝ᵥ x * v ⬝ᵥ w :=
  by
  simp only [vec3_dot_product, cross_apply, cons_vec_append, cons_vec_bit0_eq_alt0, cons_val_one,
    cons_vec_alt0, LinearMap.mk₂_apply, cons_val_zero, head_cons, empty_vec_append]
  ring_nf
#align cross_dot_cross cross_dot_cross
-/

end ProductsProperties

section LeibnizProperties

#print leibniz_cross /-
/-- The cross product satisfies the Leibniz lie property. -/
theorem leibniz_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) = u ×₃ v ×₃ w + v ×₃ (u ×₃ w) :=
  by
  dsimp only [cross_apply]
  ext i
  fin_cases i <;> norm_num <;> ring
#align leibniz_cross leibniz_cross
-/

#print Cross.lieRing /-
/-- The three-dimensional vectors together with the operations + and ×₃ form a Lie ring.
    Note we do not make this an instance as a conflicting one already exists
    via `lie_ring.of_associative_ring`. -/
def Cross.lieRing : LieRing (Fin 3 → R) :=
  { Pi.addCommGroup with
    bracket := fun u v => u ×₃ v
    add_lie := LinearMap.map_add₂ _
    lie_add := fun u => LinearMap.map_add _
    lie_self := cross_self
    leibniz_lie := leibniz_cross }
#align cross.lie_ring Cross.lieRing
-/

attribute [local instance] Cross.lieRing

#print cross_cross /-
theorem cross_cross (u v w : Fin 3 → R) : u ×₃ v ×₃ w = u ×₃ (v ×₃ w) - v ×₃ (u ×₃ w) :=
  lie_lie u v w
#align cross_cross cross_cross
-/

#print jacobi_cross /-
/-- Jacobi identity: For a cross product of three vectors,
    their sum over the three even permutations is equal to the zero vector. -/
theorem jacobi_cross (u v w : Fin 3 → R) : u ×₃ (v ×₃ w) + v ×₃ (w ×₃ u) + w ×₃ (u ×₃ v) = 0 :=
  lie_jacobi u v w
#align jacobi_cross jacobi_cross
-/

end LeibnizProperties

