/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.basic
! leanprover-community/mathlib commit 28aa996fc6fb4317f0083c4e6daf79878d81be33
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.Convex.Uniform
import Mathbin.Analysis.NormedSpace.Completion
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.LinearAlgebra.BilinearForm

/-!
# Inner product space

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the pair of assumptions
`[inner_product_space 𝕜 E] [complete_space E]`.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `is_R_or_C` typeclass.

This file proves general results on inner product spaces. For the specific construction of an inner
product structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `euclidean_space` in
`analysis.inner_product_space.pi_L2`.

## Main results

- We define the class `inner_product_space 𝕜 E` extending `normed_space 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `is_R_or_C` typeclass.
- We show that the inner product is continuous, `continuous_inner`, and bundle it as the
  the continuous sesquilinear map `innerSL` (see also `innerₛₗ` for the non-continuous version).
- We define `orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.  Bessel's inequality,
  `orthonormal.tsum_inner_products_le`, states that given an orthonormal set `v` and a vector `x`,
  the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more than the norm-square of
  `x`. For the existence of orthonormal bases, Hilbert bases, etc., see the file
  `analysis.inner_product_space.projection`.
- The `orthogonal_complement` of a submodule `K` is defined, and basic API established.  Some of
  the more subtle results about the orthogonal complement are delayed to
  `analysis.inner_product_space.projection`.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open IsROrC Real Filter

open BigOperators Topology ComplexConjugate

variable {𝕜 E F : Type _} [IsROrC 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class HasInner (𝕜 E : Type _) where
  inner : E → E → 𝕜
#align has_inner HasInner

export HasInner (inner)

-- mathport name: «expr⟪ , ⟫_ℝ»
notation "⟪" x ", " y "⟫_ℝ" => @inner ℝ _ _ x y

-- mathport name: «expr⟪ , ⟫_ℂ»
notation "⟪" x ", " y "⟫_ℂ" => @inner ℂ _ _ x y

section Notations

-- mathport name: inner.real
scoped[RealInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

-- mathport name: inner.complex
scoped[ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

end Notations

/-- An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class InnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] extends NormedAddCommGroup E,
  NormedSpace 𝕜 E, HasInner 𝕜 E where
  norm_sq_eq_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  conj_sym : ∀ x y, conj (inner y x) = inner x y
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
#align inner_product_space InnerProductSpace

attribute [nolint dangerous_instance] InnerProductSpace.toNormedAddCommGroup

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/


-- note [is_R_or_C instance]
/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_nonempty_instance]
structure InnerProductSpace.Core (𝕜 : Type _) (F : Type _) [IsROrC 𝕜] [AddCommGroup F]
  [Module 𝕜 F] where
  inner : F → F → 𝕜
  conj_sym : ∀ x y, conj (inner y x) = inner x y
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  definite : ∀ x, inner x x = 0 → x = 0
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
#align inner_product_space.core InnerProductSpace.Core

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

namespace InnerProductSpace.ofCore

variable [AddCommGroup F] [Module 𝕜 F] [c : InnerProductSpace.Core 𝕜 F]

include c

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

-- mathport name: exprnorm_sqK
local notation "norm_sqK" => @IsROrC.normSq 𝕜 _

-- mathport name: exprreK
local notation "reK" => @IsROrC.re 𝕜 _

-- mathport name: exprabsK
local notation "absK" => @IsROrC.abs 𝕜 _

-- mathport name: exprext_iff
local notation "ext_iff" => @IsROrC.ext_iff 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `inner_product_space.core` structure. -/
def toHasInner : HasInner 𝕜 F where inner := c.inner
#align inner_product_space.of_core.to_has_inner InnerProductSpace.OfCore.toHasInner

attribute [local instance] to_has_inner

/-- The norm squared function for `inner_product_space.core` structure. -/
def normSq (x : F) :=
  reK ⟪x, x⟫
#align inner_product_space.of_core.norm_sq InnerProductSpace.OfCore.normSq

-- mathport name: exprnorm_sqF
local notation "norm_sqF" => @normSq 𝕜 F _ _ _ _

theorem inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_sym x y
#align inner_product_space.of_core.inner_conj_sym InnerProductSpace.OfCore.inner_conj_sym

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _
#align inner_product_space.of_core.inner_self_nonneg InnerProductSpace.OfCore.inner_self_nonneg

theorem inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 := by
  rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp [inner_conj_sym]
#align inner_product_space.of_core.inner_self_nonneg_im InnerProductSpace.OfCore.inner_self_nonneg_im

theorem inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im
#align inner_product_space.of_core.inner_self_im_zero InnerProductSpace.OfCore.inner_self_im_zero

theorem inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _
#align inner_product_space.of_core.inner_add_left InnerProductSpace.OfCore.inner_add_left

theorem inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_sym, inner_add_left, RingHom.map_add] <;> simp only [inner_conj_sym]
#align inner_product_space.of_core.inner_add_right InnerProductSpace.OfCore.inner_add_right

theorem inner_normSq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ :=
  by
  rw [ext_iff]
  exact ⟨by simp only [of_real_re] <;> rfl, by simp only [inner_self_nonneg_im, of_real_im]⟩
#align inner_product_space.of_core.inner_norm_sq_eq_inner_self InnerProductSpace.OfCore.inner_normSq_eq_inner_self

theorem inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_sym, conj_re]
#align inner_product_space.of_core.inner_re_symm InnerProductSpace.OfCore.inner_re_symm

theorem inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_sym, conj_im]
#align inner_product_space.of_core.inner_im_symm InnerProductSpace.OfCore.inner_im_symm

theorem inner_smul_left {x y : F} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _
#align inner_product_space.of_core.inner_smul_left InnerProductSpace.OfCore.inner_smul_left

theorem inner_smul_right {x y : F} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_smul_left] <;> simp only [conj_conj, inner_conj_sym, RingHom.map_mul]
#align inner_product_space.of_core.inner_smul_right InnerProductSpace.OfCore.inner_smul_right

theorem inner_zero_left {x : F} : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left] <;> simp only [zero_mul, RingHom.map_zero]
#align inner_product_space.of_core.inner_zero_left InnerProductSpace.OfCore.inner_zero_left

theorem inner_zero_right {x : F} : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_sym, inner_zero_left] <;> simp only [RingHom.map_zero]
#align inner_product_space.of_core.inner_zero_right InnerProductSpace.OfCore.inner_zero_right

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  Iff.intro (c.definite _)
    (by
      rintro rfl
      exact inner_zero_left)
#align inner_product_space.of_core.inner_self_eq_zero InnerProductSpace.OfCore.inner_self_eq_zero

theorem inner_self_re_to_K {x : F} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_nonneg_im]
#align inner_product_space.of_core.inner_self_re_to_K InnerProductSpace.OfCore.inner_self_re_to_K

theorem inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ := by rw [← inner_conj_sym, abs_conj]
#align inner_product_space.of_core.inner_abs_conj_sym InnerProductSpace.OfCore.inner_abs_conj_sym

theorem inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
  by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp
#align inner_product_space.of_core.inner_neg_left InnerProductSpace.OfCore.inner_neg_left

theorem inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_neg_left] <;> simp only [RingHom.map_neg, inner_conj_sym]
#align inner_product_space.of_core.inner_neg_right InnerProductSpace.OfCore.inner_neg_right

theorem inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
#align inner_product_space.of_core.inner_sub_left InnerProductSpace.OfCore.inner_sub_left

theorem inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]
#align inner_product_space.of_core.inner_sub_right InnerProductSpace.OfCore.inner_sub_right

theorem inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
  by
  rw [← inner_conj_sym, mul_comm]
  exact re_eq_abs_of_mul_conj (inner y x)
#align inner_product_space.of_core.inner_mul_conj_re_abs InnerProductSpace.OfCore.inner_mul_conj_re_abs

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right] <;> ring
#align inner_product_space.of_core.inner_add_add_self InnerProductSpace.OfCore.inner_add_add_self

-- Expand `inner (x - y) (x - y)`
theorem inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right] <;> ring
#align inner_product_space.of_core.inner_sub_sub_self InnerProductSpace.OfCore.inner_sub_sub_self

/-- **Cauchy–Schwarz inequality**. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le (x y : F) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  by
  by_cases hy : y = 0
  · rw [hy]
    simp only [IsROrC.abs_zero, inner_zero_left, mul_zero, AddMonoidHom.map_zero]
  · change y ≠ 0 at hy
    have hy' : ⟪y, y⟫ ≠ 0 := fun h => by rw [inner_self_eq_zero] at h <;> exact hy h
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫ :=
      by
      rw [mul_div_assoc]
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ := by
        rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul]
      rw [this, div_eq_mul_inv, one_mul, ← div_eq_mul_inv]
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by simp only [inner_self_re_to_K]
    have h₅ : re ⟪y, y⟫ > 0 :=
      by
      refine' lt_of_le_of_ne inner_self_nonneg _
      intro H
      apply hy'
      rw [ext_iff]
      exact ⟨by simp only [H, zero_re'], by simp only [inner_self_nonneg_im, AddMonoidHom.map_zero]⟩
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅
    have hmain :=
      calc
        0 ≤ re ⟪x - T • y, x - T • y⟫ := inner_self_nonneg
        _ = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫ := by
          simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂, neg_mul,
            AddMonoidHom.map_add, mul_re, conj_im, AddMonoidHom.map_sub, mul_neg, conj_re, neg_neg]
        _ = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫) := by
          simp only [inner_smul_left, inner_smul_right, mul_assoc]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫) := by
          field_simp [-mul_re, inner_conj_sym, hT, map_div₀, h₁, h₃]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫) := by rw [← mul_div_right_comm]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫) := by conv_lhs => rw [h₄]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by rw [div_re_of_real]
        _ = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by rw [inner_mul_conj_re_abs]
        _ = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ := by rw [IsROrC.abs_mul]
        
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith
    have := (mul_le_mul_right h₅).mpr hmain'
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this
#align inner_product_space.of_core.inner_mul_inner_self_le InnerProductSpace.OfCore.inner_mul_inner_self_le

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def toHasNorm : HasNorm F where norm x := sqrt (re ⟪x, x⟫)
#align inner_product_space.of_core.to_has_norm InnerProductSpace.OfCore.toHasNorm

attribute [local instance] to_has_norm

theorem norm_eq_sqrt_inner (x : F) : ‖x‖ = sqrt (re ⟪x, x⟫) :=
  rfl
#align inner_product_space.of_core.norm_eq_sqrt_inner InnerProductSpace.OfCore.norm_eq_sqrt_inner

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]
#align inner_product_space.of_core.inner_self_eq_norm_mul_norm InnerProductSpace.OfCore.inner_self_eq_norm_mul_norm

theorem sqrt_normSq_eq_norm {x : F} : sqrt (norm_sqF x) = ‖x‖ :=
  rfl
#align inner_product_space.of_core.sqrt_norm_sq_eq_norm InnerProductSpace.OfCore.sqrt_normSq_eq_norm

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : F) : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    (by
      have H : ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) = re ⟪y, y⟫ * re ⟪x, x⟫ :=
        by
        simp only [inner_self_eq_norm_mul_norm]
        ring
      rw [H]
      conv =>
        lhs
        congr
        rw [inner_abs_conj_sym]
      exact inner_mul_inner_self_le y x)
#align inner_product_space.of_core.abs_inner_le_norm InnerProductSpace.OfCore.abs_inner_le_norm

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => sqrt (re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y =>
        by
        have h₁ : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := abs_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ abs ⟪x, y⟫ := re_le_abs _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := by linarith
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_sym, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) :=
          by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun x hx =>
        (inner_self_eq_zero : ⟪x, x⟫ = 0 ↔ x = 0).1 <|
          by
          change sqrt (re ⟪x, x⟫) = 0 at hx
          rw [sqrt_eq_zero inner_self_nonneg] at hx
          exact ext (by simp [hx]) (by simp [inner_self_im_zero]) }
#align inner_product_space.of_core.to_normed_add_comm_group InnerProductSpace.OfCore.toNormedAddCommGroup

attribute [local instance] to_normed_add_comm_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def toNormedSpace : NormedSpace 𝕜 F
    where norm_smul_le r x :=
    by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ← inner_norm_sq_eq_inner_self,
      of_real_re]
    · simp [sqrt_norm_sq_eq_norm, IsROrC.sqrt_normSq_eq_norm]
    · exact norm_sq_nonneg r
#align inner_product_space.of_core.to_normed_space InnerProductSpace.OfCore.toNormedSpace

end InnerProductSpace.ofCore

/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (c : InnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  by
  letI : NormedAddCommGroup F := @InnerProductSpace.OfCore.toNormedAddCommGroup 𝕜 F _ _ _ c
  letI : NormedSpace 𝕜 F := @InnerProductSpace.OfCore.toNormedSpace 𝕜 F _ _ _ c
  exact
    { c with
      norm_sq_eq_inner := fun x =>
        by
        have h₁ : ‖x‖ ^ 2 = sqrt (re (c.inner x x)) ^ 2 := rfl
        have h₂ : 0 ≤ re (c.inner x x) := InnerProductSpace.OfCore.inner_self_nonneg
        simp [h₁, sq_sqrt, h₂] }
#align inner_product_space.of_core InnerProductSpace.ofCore

/-! ### Properties of inner product spaces -/


variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

variable [dec_E : DecidableEq E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- mathport name: exprIK
local notation "IK" => @IsROrC.i 𝕜 _

-- mathport name: exprabsR
local notation "absR" => Abs.abs

-- mathport name: exprabsK
local notation "absK" => @IsROrC.abs 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_inner)

section BasicProperties

@[simp]
theorem inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_sym _ _
#align inner_conj_sym inner_conj_sym

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_sym ℝ _ _ _ x y
#align real_inner_comm real_inner_comm

theorem inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
  ⟨fun h => by simp [← inner_conj_sym, h], fun h => by simp [← inner_conj_sym, h]⟩
#align inner_eq_zero_sym inner_eq_zero_sym

@[simp]
theorem inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 := by
  rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp
#align inner_self_nonneg_im inner_self_nonneg_im

theorem inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im
#align inner_self_im_zero inner_self_im_zero

theorem inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _
#align inner_add_left inner_add_left

theorem inner_add_right {x y z : E} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ :=
  by
  rw [← inner_conj_sym, inner_add_left, RingHom.map_add]
  simp only [inner_conj_sym]
#align inner_add_right inner_add_right

theorem inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_sym, conj_re]
#align inner_re_symm inner_re_symm

theorem inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_sym, conj_im]
#align inner_im_symm inner_im_symm

theorem inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  InnerProductSpace.smul_left _ _ _
#align inner_smul_left inner_smul_left

theorem real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left
#align real_inner_smul_left real_inner_smul_left

theorem inner_smul_real_left {x y : E} {r : ℝ} : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ :=
  by
  rw [inner_smul_left, conj_of_real, Algebra.smul_def]
  rfl
#align inner_smul_real_left inner_smul_real_left

theorem inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_sym]
#align inner_smul_right inner_smul_right

theorem real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right
#align real_inner_smul_right real_inner_smul_right

theorem inner_smul_real_right {x y : E} {r : ℝ} : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ :=
  by
  rw [inner_smul_right, Algebra.smul_def]
  rfl
#align inner_smul_real_right inner_smul_real_right

/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫) (fun x y z => inner_add_right)
    (fun r x y => inner_smul_right) (fun x y z => inner_add_left) fun r x y => inner_smul_left
#align sesq_form_of_inner sesqFormOfInner

/-- The real inner product as a bilinear form. -/
@[simps]
def bilinFormOfRealInner : BilinForm ℝ F
    where
  bilin := inner
  bilin_add_left x y z := inner_add_left
  bilin_smul_left a x y := inner_smul_left
  bilin_add_right x y z := inner_add_right
  bilin_smul_right a x y := inner_smul_right
#align bilin_form_of_real_inner bilinFormOfRealInner

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
  (sesqFormOfInner x).map_sum
#align sum_inner sum_inner

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
  (LinearMap.flip sesqFormOfInner x).map_sum
#align inner_sum inner_sum

/-- An inner product with a sum on the left, `finsupp` version. -/
theorem Finsupp.sum_inner {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪l.Sum fun (i : ι) (a : 𝕜) => a • v i, x⟫ = l.Sum fun (i : ι) (a : 𝕜) => conj a • ⟪v i, x⟫ :=
  by
  convert sum_inner l.support (fun a => l a • v a) x
  simp only [inner_smul_left, Finsupp.sum, smul_eq_mul]
#align finsupp.sum_inner Finsupp.sum_inner

/-- An inner product with a sum on the right, `finsupp` version. -/
theorem Finsupp.inner_sum {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪x, l.Sum fun (i : ι) (a : 𝕜) => a • v i⟫ = l.Sum fun (i : ι) (a : 𝕜) => a • ⟪x, v i⟫ :=
  by
  convert inner_sum l.support (fun a => l a • v a) x
  simp only [inner_smul_right, Finsupp.sum, smul_eq_mul]
#align finsupp.inner_sum Finsupp.inner_sum

theorem Dfinsupp.sum_inner {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪l.Sum f, x⟫ = l.Sum fun i a => ⟪f i a, x⟫ := by
  simp (config := { contextual := true }) only [Dfinsupp.sum, sum_inner, smul_eq_mul]
#align dfinsupp.sum_inner Dfinsupp.sum_inner

theorem Dfinsupp.inner_sum {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.Sum f⟫ = l.Sum fun i a => ⟪x, f i a⟫ := by
  simp (config := { contextual := true }) only [Dfinsupp.sum, inner_sum, smul_eq_mul]
#align dfinsupp.inner_sum Dfinsupp.inner_sum

@[simp]
theorem inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]
#align inner_zero_left inner_zero_left

theorem inner_re_zero_left {x : E} : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]
#align inner_re_zero_left inner_re_zero_left

@[simp]
theorem inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_sym, inner_zero_left, RingHom.map_zero]
#align inner_zero_right inner_zero_right

theorem inner_re_zero_right {x : E} : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]
#align inner_re_zero_right inner_re_zero_right

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ := by
  rw [← norm_sq_eq_inner] <;> exact pow_nonneg (norm_nonneg x) 2
#align inner_self_nonneg inner_self_nonneg

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ x
#align real_inner_self_nonneg real_inner_self_nonneg

@[simp]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  by
  constructor
  · intro h
    have h₁ : re ⟪x, x⟫ = 0 := by rw [IsROrC.ext_iff] at h <;> simp only [h.1, zero_re']
    rw [← norm_sq_eq_inner x] at h₁
    rw [← norm_eq_zero]
    exact pow_eq_zero h₁
  · rintro rfl
    exact inner_zero_left
#align inner_self_eq_zero inner_self_eq_zero

@[simp]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 :=
  by
  constructor
  · intro h
    rw [← inner_self_eq_zero]
    have H₁ : re ⟪x, x⟫ ≥ 0 := inner_self_nonneg
    have H₂ : re ⟪x, x⟫ = 0 := le_antisymm h H₁
    rw [IsROrC.ext_iff]
    exact ⟨by simp [H₂], by simp [inner_self_nonneg_im]⟩
  · rintro rfl
    simp only [inner_zero_left, AddMonoidHom.map_zero]
#align inner_self_nonpos inner_self_nonpos

theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
  by
  have h := @inner_self_nonpos ℝ F _ _ x
  simpa using h
#align real_inner_self_nonpos real_inner_self_nonpos

@[simp]
theorem inner_self_re_to_K {x : E} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  IsROrC.ext_iff.2 ⟨by simp only [of_real_re], by simp only [inner_self_nonneg_im, of_real_im]⟩
#align inner_self_re_to_K inner_self_re_to_K

theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ ^ 2 : 𝕜) :=
  by
  suffices (IsROrC.re ⟪x, x⟫ : 𝕜) = ‖x‖ ^ 2 by simpa only [inner_self_re_to_K] using this
  exact_mod_cast (norm_sq_eq_inner x).symm
#align inner_self_eq_norm_sq_to_K inner_self_eq_norm_sq_to_K

theorem inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
  by
  conv_rhs => rw [← inner_self_re_to_K]
  symm
  exact IsROrC.abs_of_nonneg inner_self_nonneg
#align inner_self_re_abs inner_self_re_abs

theorem inner_self_abs_to_K {x : E} : (absK ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  by
  rw [← inner_self_re_abs]
  exact inner_self_re_to_K
#align inner_self_abs_to_K inner_self_abs_to_K

theorem real_inner_self_abs {x : F} : absR ⟪x, x⟫_ℝ = ⟪x, x⟫_ℝ :=
  by
  have h := @inner_self_abs_to_K ℝ F _ _ x
  simpa using h
#align real_inner_self_abs real_inner_self_abs

theorem inner_abs_conj_sym {x y : E} : abs ⟪x, y⟫ = abs ⟪y, x⟫ := by rw [← inner_conj_sym, abs_conj]
#align inner_abs_conj_sym inner_abs_conj_sym

@[simp]
theorem inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ :=
  by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp
#align inner_neg_left inner_neg_left

@[simp]
theorem inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_neg_left] <;> simp only [RingHom.map_neg, inner_conj_sym]
#align inner_neg_right inner_neg_right

theorem inner_neg_neg {x y : E} : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp
#align inner_neg_neg inner_neg_neg

@[simp]
theorem inner_self_conj {x : E} : ⟪x, x⟫† = ⟪x, x⟫ := by
  rw [IsROrC.ext_iff] <;> exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im_zero, neg_zero]⟩
#align inner_self_conj inner_self_conj

theorem inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]
#align inner_sub_left inner_sub_left

theorem inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]
#align inner_sub_right inner_sub_right

theorem inner_mul_conj_re_abs {x y : E} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) :=
  by
  rw [← inner_conj_sym, mul_comm]
  exact re_eq_abs_of_mul_conj (inner y x)
#align inner_mul_conj_re_abs inner_mul_conj_re_abs

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self {x y : E} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right] <;> ring
#align inner_add_add_self inner_add_add_self

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self {x y : F} : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
  by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_sym] <;> rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring
#align real_inner_add_add_self real_inner_add_add_self

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self {x y : E} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right] <;> ring
#align inner_sub_sub_self inner_sub_sub_self

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
  by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_sym] <;> rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring
#align real_inner_sub_sub_self real_inner_sub_sub_self

variable (𝕜)

include 𝕜

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← inner_self_eq_zero, inner_sub_right, sub_eq_zero, h (x - y)]
#align ext_inner_left ext_inner_left

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← inner_self_eq_zero, inner_sub_left, sub_eq_zero, h (x - y)]
#align ext_inner_right ext_inner_right

omit 𝕜

variable {𝕜}

/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]
#align parallelogram_law parallelogram_law

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:72:18: unsupported non-interactive tactic tactic.field_simp.ne_zero -/
/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
theorem inner_mul_inner_self_le (x y : E) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  by
  by_cases hy : y = 0
  · rw [hy]
    simp only [IsROrC.abs_zero, inner_zero_left, mul_zero, AddMonoidHom.map_zero]
  · have hy' : ⟪y, y⟫ ≠ 0 := inner_self_eq_zero.not.2 hy
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫ :=
      by
      rw [mul_div_assoc]
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ := by
        rw [div_mul_eq_div_mul_one_div, div_self hy', one_mul]
      rw [this, div_eq_mul_inv, one_mul, ← div_eq_mul_inv]
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := inner_self_re_to_K.symm
    have h₅ : re ⟪y, y⟫ > 0 :=
      by
      refine' lt_of_le_of_ne inner_self_nonneg _
      intro H
      apply hy'
      rw [IsROrC.ext_iff]
      exact ⟨by simp only [H, zero_re'], by simp only [inner_self_nonneg_im, AddMonoidHom.map_zero]⟩
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gt h₅
    have hmain :=
      calc
        0 ≤ re ⟪x - T • y, x - T • y⟫ := inner_self_nonneg
        _ = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫ := by
          simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, h₁, h₂, neg_mul,
            AddMonoidHom.map_add, conj_im, AddMonoidHom.map_sub, mul_neg, conj_re, neg_neg, mul_re]
        _ = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫) := by
          simp only [inner_smul_left, inner_smul_right, mul_assoc]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫) := by
          simp (disch :=
            run_tac
              tactic.field_simp.ne_zero) only [map_div₀,
            h₃, inner_conj_sym, sub_add_cancel, field_simps]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫) := by rw [← mul_div_right_comm]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫) := by conv_lhs => rw [h₄]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by rw [div_re_of_real]
        _ = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by rw [inner_mul_conj_re_abs]
        _ = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ := by rw [IsROrC.abs_mul]
        
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by linarith
    have := (mul_le_mul_right h₅).mpr hmain'
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this
#align inner_mul_inner_self_le inner_mul_inner_self_le

/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
  by
  have h₁ : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_sym] <;> rfl
  have h₂ := @inner_mul_inner_self_le ℝ F _ _ x y
  dsimp at h₂
  have h₃ := abs_mul_abs_self ⟪x, y⟫_ℝ
  rw [h₁] at h₂
  simpa [h₃] using h₂
#align real_inner_mul_inner_self_le real_inner_mul_inner_self_le

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linearIndependent_of_ne_zero_of_inner_eq_zero {ι : Type _} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v :=
  by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have h' : g i * inner (v i) (v i) = inner (v i) (∑ j in s, g j • v j) :=
    by
    rw [inner_sum]
    symm
    convert Finset.sum_eq_single i _ _
    · rw [inner_smul_right]
    · intro j hj hji
      rw [inner_smul_right, ho i j hji.symm, mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'
#align linear_independent_of_ne_zero_of_inner_eq_zero linearIndependent_of_ne_zero_of_inner_eq_zero

end BasicProperties

section OrthonormalSets

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

include 𝕜

/-- An orthonormal set of vectors in an `inner_product_space` -/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ ∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0
#align orthonormal Orthonormal

omit 𝕜

variable {𝕜}

include dec_ι

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
theorem orthonormal_iff_ite {v : ι → E} :
    Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜) :=
  by
  constructor
  · intro hv i j
    split_ifs
    · simp [h, inner_self_eq_norm_sq_to_K, hv.1]
    · exact hv.2 h
  · intro h
    constructor
    · intro i
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by simp [norm_sq_eq_inner, h i i]
      have h₁ : 0 ≤ ‖v i‖ := norm_nonneg _
      have h₂ : (0 : ℝ) ≤ 1 := zero_le_one
      rwa [sq_eq_sq h₁ h₂] at h'
    · intro i j hij
      simpa [hij] using h i j
#align orthonormal_iff_ite orthonormal_iff_ite

omit dec_ι

include dec_E

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {s : Set E} :
    Orthonormal 𝕜 (coe : s → E) ↔ ∀ v ∈ s, ∀ w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0 :=
  by
  rw [orthonormal_iff_ite]
  constructor
  · intro h v hv w hw
    convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1
    simp
  · rintro h ⟨v, hv⟩ ⟨w, hw⟩
    convert h v hv w hw using 1
    simp
#align orthonormal_subtype_iff_ite orthonormal_subtype_iff_ite

omit dec_E

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = l i := by
  classical simp [Finsupp.total_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv]
#align orthonormal.inner_right_finsupp Orthonormal.inner_right_finsupp

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪v i, ∑ i in s, l i • v i⟫ = l i := by
  classical simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]
#align orthonormal.inner_right_sum Orthonormal.inner_right_sum

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)
#align orthonormal.inner_right_fintype Orthonormal.inner_right_fintype

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) := by rw [← inner_conj_sym, hv.inner_right_finsupp]
#align orthonormal.inner_left_finsupp Orthonormal.inner_left_finsupp

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪∑ i in s, l i • v i, v i⟫ = conj (l i) := by
  classical simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
      Finset.sum_ite_eq', if_true]
#align orthonormal.inner_left_sum Orthonormal.inner_left_sum

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)
#align orthonormal.inner_left_fintype Orthonormal.inner_left_fintype

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₁.Sum fun i y => conj y * l₂ i := by
  simp only [l₁.total_apply _, Finsupp.sum_inner, hv.inner_right_finsupp, smul_eq_mul]
#align orthonormal.inner_finsupp_eq_sum_left Orthonormal.inner_finsupp_eq_sum_left

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₂.Sum fun i y => conj (l₁ i) * y := by
  simp only [l₂.total_apply _, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm, smul_eq_mul]
#align orthonormal.inner_finsupp_eq_sum_right Orthonormal.inner_finsupp_eq_sum_right

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
theorem Orthonormal.inner_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι → 𝕜) (s : Finset ι) :
    ⟪∑ i in s, l₁ i • v i, ∑ i in s, l₂ i • v i⟫ = ∑ i in s, conj (l₁ i) * l₂ i :=
  by
  simp_rw [sum_inner, inner_smul_left]
  refine' Finset.sum_congr rfl fun i hi => _
  rw [hv.inner_right_sum l₂ hi]
#align orthonormal.inner_sum Orthonormal.inner_sum

/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal 𝕜 v)
    {a : ι → ι → 𝕜} : (∑ i in s, ∑ j in s, a i j • ⟪v j, v i⟫) = ∑ k in s, a k k := by
  classical simp [orthonormal_iff_ite.mp hv, Finset.sum_ite_of_true]
#align orthonormal.inner_left_right_finset Orthonormal.inner_left_right_finset

/-- An orthonormal set is linearly independent. -/
theorem Orthonormal.linearIndependent {v : ι → E} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v :=
  by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using key
#align orthonormal.linear_independent Orthonormal.linearIndependent

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
theorem Orthonormal.comp {ι' : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) (f : ι' → ι)
    (hf : Function.Injective f) : Orthonormal 𝕜 (v ∘ f) := by
  classical
    rw [orthonormal_iff_ite] at hv⊢
    intro i j
    convert hv (f i) (f j) using 1
    simp [hf.eq_iff]
#align orthonormal.comp Orthonormal.comp

/-- An injective family `v : ι → E` is orthonormal if and only if `coe : (range v) → E` is
orthonormal. -/
theorem orthonormal_subtype_range {v : ι → E} (hv : Function.Injective v) :
    Orthonormal 𝕜 (coe : Set.range v → E) ↔ Orthonormal 𝕜 v :=
  by
  let f : ι ≃ Set.range v := Equiv.ofInjective v hv
  refine' ⟨fun h => h.comp f f.injective, fun h => _⟩
  rw [← Equiv.self_comp_ofInjective_symm hv]
  exact h.comp f.symm f.symm.injective
#align orthonormal_subtype_range orthonormal_subtype_range

/-- If `v : ι → E` is an orthonormal family, then `coe : (range v) → E` is an orthonormal
family. -/
theorem Orthonormal.toSubtypeRange {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (coe : Set.range v → E) :=
  (orthonormal_subtype_range hv.LinearIndependent.Injective).2 hv
#align orthonormal.to_subtype_range Orthonormal.toSubtypeRange

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
    (hi : i ∉ s) {l : ι →₀ 𝕜} (hl : l ∈ Finsupp.supported 𝕜 𝕜 s) :
    ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = 0 :=
  by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]
#align orthonormal.inner_finsupp_eq_zero Orthonormal.inner_finsupp_eq_zero

/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
theorem Orthonormal.orthonormalOfForallEqOrEqNeg {v w : ι → E} (hv : Orthonormal 𝕜 v)
    (hw : ∀ i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w := by
  classical
    rw [orthonormal_iff_ite] at *
    intro i j
    cases' hw i with hi hi <;> cases' hw j with hj hj <;> split_ifs with h <;>
      simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
        neg_eq_zero] using hv i j
#align orthonormal.orthonormal_of_forall_eq_or_eq_neg Orthonormal.orthonormalOfForallEqOrEqNeg

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/
variable (𝕜 E)

theorem orthonormalEmpty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) → E) := by
  classical simp [orthonormal_subtype_iff_ite]
#align orthonormal_empty orthonormalEmpty

variable {𝕜 E}

theorem orthonormalUnionOfDirected {η : Type _} {s : η → Set E} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, Orthonormal 𝕜 (fun x => x : s i → E)) : Orthonormal 𝕜 (fun x => x : (⋃ i, s i) → E) :=
  by
  classical
    rw [orthonormal_subtype_iff_ite]
    rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
    obtain ⟨k, hik, hjk⟩ := hs i j
    have h_orth : Orthonormal 𝕜 (fun x => x : s k → E) := h k
    rw [orthonormal_subtype_iff_ite] at h_orth
    exact h_orth x (hik hxi) y (hjk hyj)
#align orthonormal_Union_of_directed orthonormalUnionOfDirected

theorem orthonormalSUnionOfDirected {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, Orthonormal 𝕜 (fun x => x : (a : Set E) → E)) :
    Orthonormal 𝕜 (fun x => x : ⋃₀ s → E) := by
  rw [Set.unionₛ_eq_unionᵢ] <;> exact orthonormalUnionOfDirected hs.directed_coe (by simpa using h)
#align orthonormal_sUnion_of_directed orthonormalSUnionOfDirected

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (w «expr ⊇ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (u «expr ⊇ » w) -/
/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (coe : s → E)) :
    ∃ (w : _)(_ : w ⊇ s),
      Orthonormal 𝕜 (coe : w → E) ∧ ∀ (u) (_ : u ⊇ w), Orthonormal 𝕜 (coe : u → E) → u = w :=
  by
  obtain ⟨b, bi, sb, h⟩ := zorn_subset_nonempty { b | Orthonormal 𝕜 (coe : b → E) } _ _ hs
  · refine' ⟨b, sb, bi, _⟩
    exact fun u hus hu => h u hu hus
  · refine' fun c hc cc c0 => ⟨⋃₀ c, _, _⟩
    · exact orthonormalSUnionOfDirected cc.directed_on fun x xc => hc xc
    · exact fun _ => Set.subset_unionₛ_of_mem
#align exists_maximal_orthonormal exists_maximal_orthonormal

theorem Orthonormal.ne_zero {v : ι → E} (hv : Orthonormal 𝕜 v) (i : ι) : v i ≠ 0 :=
  by
  have : ‖v i‖ ≠ 0 := by
    rw [hv.1 i]
    norm_num
  simpa using this
#align orthonormal.ne_zero Orthonormal.ne_zero

open FiniteDimensional

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.LinearIndependent card_eq
#align basis_of_orthonormal_of_card_eq_finrank basisOfOrthonormalOfCardEqFinrank

@[simp]
theorem coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E}
    (hv : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) :
    (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _
#align coe_basis_of_orthonormal_of_card_eq_finrank coe_basisOfOrthonormalOfCardEqFinrank

end OrthonormalSets

section Norm

theorem norm_eq_sqrt_inner (x : E) : ‖x‖ = sqrt (re ⟪x, x⟫) :=
  calc
    ‖x‖ = sqrt (‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = sqrt (re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_inner _)
    
#align norm_eq_sqrt_inner norm_eq_sqrt_inner

theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = sqrt ⟪x, x⟫_ℝ :=
  by
  have h := @norm_eq_sqrt_inner ℝ F _ _ x
  simpa using h
#align norm_eq_sqrt_real_inner norm_eq_sqrt_real_inner

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]
#align inner_self_eq_norm_mul_norm inner_self_eq_norm_mul_norm

theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]
#align inner_self_eq_norm_sq inner_self_eq_norm_sq

theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ :=
  by
  have h := @inner_self_eq_norm_mul_norm ℝ F _ _ x
  simpa using h
#align real_inner_self_eq_norm_mul_norm real_inner_self_eq_norm_mul_norm

theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]
#align real_inner_self_eq_norm_sq real_inner_self_eq_norm_sq

/-- Expand the square -/
theorem norm_add_sq {x y : E} : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 :=
  by
  repeat' rw [sq, ← inner_self_eq_norm_mul_norm]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, AddMonoidHom.map_add]
  rw [← inner_conj_sym, conj_re]
#align norm_add_sq norm_add_sq

alias norm_add_sq ← norm_add_pow_two
#align norm_add_pow_two norm_add_pow_two

/-- Expand the square -/
theorem norm_add_sq_real {x y : F} : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  by
  have h := @norm_add_sq ℝ F _ _
  simpa using h
#align norm_add_sq_real norm_add_sq_real

alias norm_add_sq_real ← norm_add_pow_two_real
#align norm_add_pow_two_real norm_add_pow_two_real

/-- Expand the square -/
theorem norm_add_mul_self {x y : E} : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ :=
  by
  repeat' rw [← sq]
  exact norm_add_sq
#align norm_add_mul_self norm_add_mul_self

/-- Expand the square -/
theorem norm_add_mul_self_real {x y : F} :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ :=
  by
  have h := @norm_add_mul_self ℝ F _ _
  simpa using h
#align norm_add_mul_self_real norm_add_mul_self_real

/-- Expand the square -/
theorem norm_sub_sq {x y : E} : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 :=
  by
  repeat' rw [sq, ← inner_self_eq_norm_mul_norm]
  rw [inner_sub_sub_self]
  calc
    re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫) = re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫ + re ⟪y, y⟫ := by
      simp only [map_add, map_sub]
    _ = -re ⟪y, x⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by ring
    _ = -re (⟪x, y⟫†) - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by rw [inner_conj_sym]
    _ = -re ⟪x, y⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by rw [conj_re]
    _ = re ⟪x, x⟫ - 2 * re ⟪x, y⟫ + re ⟪y, y⟫ := by ring
    
#align norm_sub_sq norm_sub_sq

alias norm_sub_sq ← norm_sub_pow_two
#align norm_sub_pow_two norm_sub_pow_two

/-- Expand the square -/
theorem norm_sub_sq_real {x y : F} : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  norm_sub_sq
#align norm_sub_sq_real norm_sub_sq_real

alias norm_sub_sq_real ← norm_sub_pow_two_real
#align norm_sub_pow_two_real norm_sub_pow_two_real

/-- Expand the square -/
theorem norm_sub_mul_self {x y : E} : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ :=
  by
  repeat' rw [← sq]
  exact norm_sub_sq
#align norm_sub_mul_self norm_sub_mul_self

/-- Expand the square -/
theorem norm_sub_mul_self_real {x y : F} :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ :=
  by
  have h := @norm_sub_mul_self ℝ F _ _
  simpa using h
#align norm_sub_mul_self_real norm_sub_mul_self_real

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : E) : abs ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by
      have : ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) = re ⟪x, x⟫ * re ⟪y, y⟫
      simp only [inner_self_eq_norm_mul_norm]; ring
      rw [this]
      conv_lhs =>
        congr
        skip
        rw [inner_abs_conj_sym]
      exact inner_mul_inner_self_le _ _)
#align abs_inner_le_norm abs_inner_le_norm

theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  (IsROrC.norm_eq_abs _).le.trans (abs_inner_le_norm x y)
#align norm_inner_le_norm norm_inner_le_norm

theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y
#align nnnorm_inner_le_nnnorm nnnorm_inner_le_nnnorm

theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_abs (inner x y)) (abs_inner_le_norm x y)
#align re_inner_le_norm re_inner_le_norm

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm (x y : F) : absR ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  by
  have h := @abs_inner_le_norm ℝ F _ _ x y
  simpa using h
#align abs_real_inner_le_norm abs_real_inner_le_norm

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
#align real_inner_le_norm real_inner_le_norm

include 𝕜

theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
  by
  simp only [← inner_self_eq_norm_mul_norm]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [re.map_add]
#align parallelogram_law_with_norm parallelogram_law_with_norm

theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm x y
#align parallelogram_law_with_nnnorm parallelogram_law_with_nnnorm

omit 𝕜

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  by
  rw [norm_add_mul_self]
  ring
#align re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  by
  rw [norm_sub_mul_self]
  ring
#align re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 :=
  by
  rw [norm_add_mul_self, norm_sub_mul_self]
  ring
#align re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 :=
  by
  simp only [norm_add_mul_self, norm_sub_mul_self, inner_smul_right, I_mul_re]
  ring
#align im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + (‖x - IK • y‖ ^ 2 - ‖x + IK • y‖ ^ 2) * IK) / 4 :=
  by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]
#align inner_eq_sum_norm_sq_div_four inner_eq_sum_norm_sq_div_four

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `euclidean_geometry.dist_inversion_inversion` for inversions around a general
point. -/
theorem dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) = R ^ 2 / (‖x‖ * ‖y‖) * dist x y :=
  have hx' : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  calc
    dist ((R / ‖x‖) ^ 2 • x) ((R / ‖y‖) ^ 2 • y) =
        sqrt (‖(R / ‖x‖) ^ 2 • x - (R / ‖y‖) ^ 2 • y‖ ^ 2) :=
      by rw [dist_eq_norm, sqrt_sq (norm_nonneg _)]
    _ = sqrt ((R ^ 2 / (‖x‖ * ‖y‖)) ^ 2 * ‖x - y‖ ^ 2) :=
      congr_arg sqrt <|
        by
        field_simp [sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _)]
        ring
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _),
        sqrt_sq (div_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))),
        dist_eq_norm]
    
#align dist_div_norm_sq_smul dist_div_norm_sq_smul

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.to_uniformConvexSpace : UniformConvexSpace F :=
  ⟨fun ε hε =>
    by
    refine'
      ⟨2 - sqrt (4 - ε ^ 2), sub_pos_of_lt <| (sqrt_lt' zero_lt_two).2 _, fun x hx y hy hxy => _⟩
    · norm_num
      exact pow_pos hε _
    rw [sub_sub_cancel]
    refine' le_sqrt_of_sq_le _
    rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm x y), ← sq ‖x - y‖, hx, hy]
    norm_num
    exact pow_le_pow_of_le_left hε.le hxy _⟩
#align inner_product_space.to_uniform_convex_space InnerProductSpace.to_uniformConvexSpace

section Complex

variable {V : Type _} [InnerProductSpace ℂ V]

/-- A complex polarization identity, with a linear map
-/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
            Complex.i * ⟪T (x + Complex.i • y), x + Complex.i • y⟫_ℂ -
          Complex.i * ⟪T (x - Complex.i • y), x - Complex.i • y⟫_ℂ) /
        4 :=
  by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_i, ← pow_two, Complex.i_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring
#align inner_map_polarization inner_map_polarization

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.i * ⟪T (x + Complex.i • y), x + Complex.i • y⟫_ℂ +
          Complex.i * ⟪T (x - Complex.i • y), x - Complex.i • y⟫_ℂ) /
        4 :=
  by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_i, ← pow_two, Complex.i_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring
#align inner_map_polarization' inner_map_polarization'

/-- A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for all `x`.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 :=
  by
  constructor
  · intro hT
    ext x
    simp only [LinearMap.zero_apply, ← inner_self_eq_zero, inner_map_polarization, hT]
    norm_num
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]
#align inner_map_self_eq_zero inner_map_self_eq_zero

/--
Two linear maps `S` and `T` are equal, if and only if the identity `⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ` holds
for all `x`.
-/
theorem ext_inner_map (S T : V →ₗ[ℂ] V) : (∀ x : V, ⟪S x, x⟫_ℂ = ⟪T x, x⟫_ℂ) ↔ S = T :=
  by
  rw [← sub_eq_zero, ← inner_map_self_eq_zero]
  refine' forall_congr' fun x => _
  rw [LinearMap.sub_apply, inner_sub_left, sub_eq_zero]
#align ext_inner_map ext_inner_map

end Complex

section

variable {ι : Type _} {ι' : Type _} {ι'' : Type _}

variable {E' : Type _} [InnerProductSpace 𝕜 E']

variable {E'' : Type _} [InnerProductSpace 𝕜 E'']

/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]
#align linear_isometry.inner_map_map LinearIsometry.inner_map_map

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y
#align linear_isometry_equiv.inner_map_map LinearIsometryEquiv.inner_map_map

/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [norm_eq_sqrt_inner, h]⟩
#align linear_map.isometry_of_inner LinearMap.isometryOfInner

@[simp]
theorem LinearMap.coe_isometryOfInner (f : E →ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl
#align linear_map.coe_isometry_of_inner LinearMap.coe_isometryOfInner

@[simp]
theorem LinearMap.isometryOfInner_toLinearMap (f : E →ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl
#align linear_map.isometry_of_inner_to_linear_map LinearMap.isometryOfInner_toLinearMap

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩
#align linear_equiv.isometry_of_inner LinearEquiv.isometryOfInner

@[simp]
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl
#align linear_equiv.coe_isometry_of_inner LinearEquiv.coe_isometryOfInner

@[simp]
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl
#align linear_equiv.isometry_of_inner_to_linear_equiv LinearEquiv.isometryOfInner_toLinearEquiv

/-- A linear isometry preserves the property of being orthonormal. -/
theorem LinearIsometry.orthonormal_comp_iff {v : ι → E} (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v := by
  classical simp_rw [orthonormal_iff_ite, LinearIsometry.inner_map_map]
#align linear_isometry.orthonormal_comp_iff LinearIsometry.orthonormal_comp_iff

/-- A linear isometry preserves the property of being orthonormal. -/
theorem Orthonormal.compLinearIsometry {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) := by rwa [f.orthonormal_comp_iff]
#align orthonormal.comp_linear_isometry Orthonormal.compLinearIsometry

/-- A linear isometric equivalence preserves the property of being orthonormal. -/
theorem Orthonormal.compLinearIsometryEquiv {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) :=
  hv.compLinearIsometry f.toLinearIsometry
#align orthonormal.comp_linear_isometry_equiv Orthonormal.compLinearIsometryEquiv

/-- A linear isometric equivalence, applied with `basis.map`, preserves the property of being
orthonormal. -/
theorem Orthonormal.mapLinearIsometryEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (v.map f.toLinearEquiv) :=
  hv.compLinearIsometryEquiv f
#align orthonormal.map_linear_isometry_equiv Orthonormal.mapLinearIsometryEquiv

/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
def LinearMap.isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← v.total_repr x, ← v.total_repr y, Finsupp.apply_total, Finsupp.apply_total,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_map.isometry_of_orthonormal LinearMap.isometryOfOrthonormal

@[simp]
theorem LinearMap.coe_isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl
#align linear_map.coe_isometry_of_orthonormal LinearMap.coe_isometryOfOrthonormal

@[simp]
theorem LinearMap.isometryOfOrthonormal_toLinearMap (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl
#align linear_map.isometry_of_orthonormal_to_linear_map LinearMap.isometryOfOrthonormal_toLinearMap

/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.total_repr x, ← v.total_repr y, ← LinearEquiv.coe_coe, Finsupp.apply_total,
      Finsupp.apply_total, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_equiv.isometry_of_orthonormal LinearEquiv.isometryOfOrthonormal

@[simp]
theorem LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl
#align linear_equiv.coe_isometry_of_orthonormal LinearEquiv.coe_isometryOfOrthonormal

@[simp]
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl
#align linear_equiv.isometry_of_orthonormal_to_linear_equiv LinearEquiv.isometryOfOrthonormal_toLinearEquiv

/-- A linear isometric equivalence that sends an orthonormal basis to a given orthonormal basis. -/
def Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
  (v.Equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)
#align orthonormal.equiv Orthonormal.equiv

@[simp]
theorem Orthonormal.equiv_toLinearEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    (hv.Equiv hv' e).toLinearEquiv = v.Equiv v' e :=
  rfl
#align orthonormal.equiv_to_linear_equiv Orthonormal.equiv_toLinearEquiv

@[simp]
theorem Orthonormal.equiv_apply {ι' : Type _} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) :
    hv.Equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _
#align orthonormal.equiv_apply Orthonormal.equiv_apply

@[simp]
theorem Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) :
    hv.Equiv hv (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id.def, LinearIsometryEquiv.coe_refl]
#align orthonormal.equiv_refl Orthonormal.equiv_refl

@[simp]
theorem Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.Equiv hv' e).symm = hv'.Equiv hv e.symm :=
  v'.ext_linearIsometryEquiv fun i =>
    (hv.Equiv hv' e).Injective <| by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]
#align orthonormal.equiv_symm Orthonormal.equiv_symm

@[simp]
theorem Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' : Orthonormal 𝕜 v'')
    (e' : ι' ≃ ι'') : (hv.Equiv hv' e).trans (hv'.Equiv hv'' e') = hv.Equiv hv'' (e.trans e') :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans]
#align orthonormal.equiv_trans Orthonormal.equiv_trans

theorem Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    v.map (hv.Equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.mapEquiv _ _
#align orthonormal.map_equiv Orthonormal.map_equiv

end

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y
#align real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
#align real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
  by
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero]
  norm_num
#align norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero

/-- Pythagorean theorem, if-and-if vector inner product form using square roots. -/
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
    sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]
#align norm_add_eq_sqrt_iff_real_inner_eq_zero norm_add_eq_sqrt_iff_real_inner_eq_zero

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  by
  rw [norm_add_mul_self, add_right_cancel_iff, add_right_eq_self, mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re']
#align norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h
#align norm_add_sq_eq_norm_sq_add_norm_sq_real norm_add_sq_eq_norm_sq_add_norm_sq_real

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
  by
  rw [norm_sub_mul_self, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
    mul_eq_zero]
  norm_num
#align norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero

/-- Pythagorean theorem, subtracting vectors, if-and-if vector inner product form using square
roots. -/
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
    sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]
#align norm_sub_eq_sqrt_iff_real_inner_eq_zero norm_sub_eq_sqrt_iff_real_inner_eq_zero

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h
#align norm_sub_sq_eq_norm_sq_add_norm_sq_real norm_sub_sq_eq_norm_sq_add_norm_sq_real

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ :=
  by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← inner_self_eq_norm_mul_norm, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  constructor
  · intro h
    rw [add_comm] at h
    linarith
  · intro h
    linarith
#align real_inner_add_sub_eq_zero_iff real_inner_add_sub_eq_zero_iff

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ :=
  by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← inner_self_eq_norm_mul_norm, sub_neg_eq_add, sub_zero, map_sub, zero_re',
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]
#align norm_sub_eq_norm_add norm_sub_eq_norm_add

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : absR (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)) ≤ 1 :=
  by
  rw [_root_.abs_div]
  by_cases h : 0 = absR (‖x‖ * ‖y‖)
  · rw [← h, div_zero]
    norm_num
  · change 0 ≠ absR (‖x‖ * ‖y‖) at h
    rw [div_le_iff' (lt_of_le_of_ne (ge_iff_le.mp (_root_.abs_nonneg (‖x‖ * ‖y‖))) h)]
    convert abs_real_inner_le_norm x y using 1
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y),
      mul_one]
#align abs_real_inner_div_norm_mul_norm_le_one abs_real_inner_div_norm_mul_norm_le_one

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [real_inner_smul_left, ← real_inner_self_eq_norm_mul_norm]
#align real_inner_smul_self_left real_inner_smul_self_left

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [inner_smul_right, ← real_inner_self_eq_norm_mul_norm]
#align real_inner_smul_self_right real_inner_smul_self_right

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0)
    (hr : r ≠ 0) : abs ⟪x, r • x⟫ / (‖x‖ * ‖r • x‖) = 1 :=
  by
  have hx' : ‖x‖ ≠ 0 := by simp [norm_eq_zero, hx]
  have hr' : abs r ≠ 0 := by simp [IsROrC.abs_eq_zero, hr]
  rw [inner_smul_right, IsROrC.abs_mul, ← inner_self_re_abs, inner_self_eq_norm_mul_norm, norm_smul]
  rw [IsROrC.norm_eq_abs, ← mul_assoc, ← div_div, mul_div_cancel _ hx', ← div_div, mul_comm,
    mul_div_cancel _ hr', div_self hx']
#align abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ}
    (hx : x ≠ 0) (hr : r ≠ 0) : absR ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 :=
  by
  rw [← abs_to_real]
  exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
#align abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 :=
  by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ (absR r),
    mul_assoc, _root_.abs_of_nonneg (le_of_lt hr), div_self]
  exact mul_ne_zero (ne_of_gt hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))
#align real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 :=
  by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ (absR r),
    mul_assoc, abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self]
  exact mul_ne_zero (ne_of_lt hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))
#align real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    abs (⟪x, y⟫ / (‖x‖ * ‖y‖)) = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, inner_zero_left, zero_div] at h
      norm_num at h
    refine' And.intro hx0 _
    set r := ⟪x, y⟫ / (‖x‖ * ‖x‖) with hr
    use r
    set t := y - r • x with ht
    have ht0 : ⟪x, t⟫ = 0 :=
      by
      rw [ht, inner_sub_right, inner_smul_right, hr]
      norm_cast
      rw [← inner_self_eq_norm_mul_norm, inner_self_re_to_K,
        div_mul_cancel _ fun h => hx0 (inner_self_eq_zero.1 h), sub_self]
    replace h : ‖r • x‖ / ‖t + r • x‖ = 1
    · rw [← sub_add_cancel y (r • x), ← ht, inner_add_right, ht0, zero_add, inner_smul_right,
        IsROrC.abs_div, IsROrC.abs_mul, ← inner_self_re_abs, inner_self_eq_norm_mul_norm] at h
      norm_cast  at h
      rwa [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm, ← mul_assoc, mul_comm,
        mul_div_mul_left _ _ fun h => hx0 (norm_eq_zero.1 h), ← IsROrC.norm_eq_abs, ← norm_smul] at
        h
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_smul, norm_zero, zero_div] at h
      norm_num at h
    refine' And.intro hr0 _
    have h2 : ‖r • x‖ ^ 2 = ‖t + r • x‖ ^ 2 := by rw [eq_of_div_eq_one h]
    replace h2 : ⟪r • x, r • x⟫ = ⟪t, t⟫ + ⟪t, r • x⟫ + ⟪r • x, t⟫ + ⟪r • x, r • x⟫
    · rw [sq, sq, ← inner_self_eq_norm_mul_norm, ← inner_self_eq_norm_mul_norm] at h2
      have h2' := congr_arg (fun z : ℝ => (z : 𝕜)) h2
      simp_rw [inner_self_re_to_K, inner_add_add_self] at h2'
      exact h2'
    conv at h2 in ⟪r • x, t⟫ => rw [inner_smul_left, ht0, mul_zero]
    symm at h2
    have h₁ : ⟪t, r • x⟫ = 0 :=
      by
      rw [inner_smul_right, ← inner_conj_sym, ht0]
      simp
    rw [add_zero, h₁, add_left_eq_self, add_zero, inner_self_eq_zero] at h2
    rw [h2] at ht
    exact eq_of_sub_eq_zero ht.symm
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy, IsROrC.abs_div]
    norm_cast
    rw [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm]
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
#align abs_inner_div_norm_mul_norm_eq_one_iff abs_inner_div_norm_mul_norm_eq_one_iff

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    absR (⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ y = r • x :=
  by
  have := @abs_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ x y
  simpa [coe_real_eq_id] using this
#align abs_real_inner_div_norm_mul_norm_eq_one_iff abs_real_inner_div_norm_mul_norm_eq_one_iff

/-- If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem abs_inner_eq_norm_iff (x y : E) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    abs ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  by
  have hxy0 : ‖x‖ * ‖y‖ ≠ 0 := mul_ne_zero (norm_eq_zero.not.2 hx0) (norm_eq_zero.not.2 hy0)
  have h₁ : abs ⟪x, y⟫ = ‖x‖ * ‖y‖ ↔ abs (⟪x, y⟫ / (‖x‖ * ‖y‖)) = 1 :=
    by
    rw [← algebraMap.coe_mul, IsROrC.abs_div, IsROrC.abs_of_nonneg, div_eq_one_iff_eq hxy0]
    positivity
  rw [h₁, abs_inner_div_norm_mul_norm_eq_one_iff x y]
  exact and_iff_right hx0
#align abs_inner_eq_norm_iff abs_inner_eq_norm_iff

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x :=
  by
  constructor
  · intro h
    have ha := h
    apply_fun absR  at ha
    norm_num at ha
    rcases(abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    use hx, r
    refine' And.intro _ hy
    by_contra hrneg
    rw [hy] at h
    rw [real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx
        (lt_of_le_of_ne (le_of_not_lt hrneg) hr)] at
      h
    norm_num at h
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy]
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr
#align real_inner_div_norm_mul_norm_eq_one_iff real_inner_div_norm_mul_norm_eq_one_iff

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x :=
  by
  constructor
  · intro h
    have ha := h
    apply_fun absR  at ha
    norm_num at ha
    rcases(abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    use hx, r
    refine' And.intro _ hy
    by_contra hrpos
    rw [hy] at h
    rw [real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx
        (lt_of_le_of_ne (le_of_not_lt hrpos) hr.symm)] at
      h
    norm_num at h
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy]
    exact real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr
#align real_inner_div_norm_mul_norm_eq_neg_one_iff real_inner_div_norm_mul_norm_eq_neg_one_iff

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y :=
  by
  by_cases h : x = 0 ∨ y = 0
  -- WLOG `x` and `y` are nonzero
  · cases h <;> simp [h]
  calc
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ ‖x‖ * ‖y‖ = re ⟪x, y⟫ :=
      by
      norm_cast
      constructor
      · intro h'
        simp [h']
      · have cauchy_schwarz := abs_inner_le_norm x y
        intro h'
        rw [h'] at cauchy_schwarz⊢
        rwa [re_eq_self_of_le]
    _ ↔ 2 * ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖ - re ⟪x, y⟫) = 0 := by
      simp [h, show (2 : ℝ) ≠ 0 by norm_num, sub_eq_zero]
    _ ↔ ‖(‖y‖ : 𝕜) • x - (‖x‖ : 𝕜) • y‖ * ‖(‖y‖ : 𝕜) • x - (‖x‖ : 𝕜) • y‖ = 0 :=
      by
      simp only [norm_sub_mul_self, inner_smul_left, inner_smul_right, norm_smul, conj_of_real,
        IsROrC.norm_eq_abs, abs_of_real, of_real_im, of_real_re, mul_re, abs_norm_eq_norm]
      refine' Eq.congr _ rfl
      ring
    _ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y := by simp [norm_sub_eq_zero_iff]
    
#align inner_eq_norm_mul_iff inner_eq_norm_mul_iff

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff
#align inner_eq_norm_mul_iff_real inner_eq_norm_mul_iff_real

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_norm_mul_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫ = 1 ↔ x = y := by convert inner_eq_norm_mul_iff using 2 <;> simp [hx, hy]
#align inner_eq_norm_mul_iff_of_norm_one inner_eq_norm_mul_iff_of_norm_one

theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
  calc
    ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x ≠ ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real
    
#align inner_lt_norm_mul_iff_real inner_lt_norm_mul_iff_real

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by convert inner_lt_norm_mul_iff_real <;> simp [hx, hy]
#align inner_lt_one_iff_real_of_norm_one inner_lt_one_iff_real_of_norm_one

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type _} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ}
    (v₁ : ι₁ → F) (h₁ : (∑ i in s₁, w₁ i) = 0) {ι₂ : Type _} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ}
    (v₂ : ι₂ → F) (h₂ : (∑ i in s₂, w₂ i) = 0) :
    ⟪∑ i₁ in s₁, w₁ i₁ • v₁ i₁, ∑ i₂ in s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (‖v₁ i₁ - v₂ i₂‖ * ‖v₁ i₁ - v₂ i₂‖)) / 2 :=
  by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same,
    ← div_add_div_same, mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, zero_mul, mul_zero,
    Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div, Finset.sum_div,
    mul_div_assoc, mul_assoc]
#align inner_sum_smul_sum_smul_of_sum_eq_zero inner_sum_smul_sum_smul_of_sum_eq_zero

/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) (fun _ _ _ => inner_add_left)
    (fun _ _ _ => inner_smul_left) (fun _ _ _ => inner_add_right) fun _ _ _ => inner_smul_right
#align innerₛₗ innerₛₗ

@[simp]
theorem innerₛₗ_apply_coe (v : E) : (innerₛₗ v : E → 𝕜) = fun w => ⟪v, w⟫ :=
  rfl
#align innerₛₗ_apply_coe innerₛₗ_apply_coe

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ v w = ⟪v, w⟫ :=
  rfl
#align innerₛₗ_apply innerₛₗ_apply

/-- The inner product as a continuous sesquilinear map. Note that `to_dual_map` (resp. `to_dual`)
in `inner_product_space.dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ innerₛₗ 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply]
#align innerSL innerSL

@[simp]
theorem innerSL_apply_coe (v : E) : (innerSL v : E → 𝕜) = fun w => ⟪v, w⟫ :=
  rfl
#align innerSL_apply_coe innerSL_apply_coe

@[simp]
theorem innerSL_apply (v w : E) : innerSL v w = ⟪v, w⟫ :=
  rfl
#align innerSL_apply innerSL_apply

/-- `innerSL` is an isometry. Note that the associated `linear_isometry` is defined in
`inner_product_space.dual` as `to_dual_map`.  -/
@[simp]
theorem innerSL_apply_norm {x : E} : ‖(innerSL x : E →L[𝕜] 𝕜)‖ = ‖x‖ :=
  by
  refine'
    le_antisymm
      ((innerSL x : E →L[𝕜] 𝕜).op_norm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) _
  cases' eq_or_lt_of_le (norm_nonneg x) with h h
  · have : x = 0 := norm_eq_zero.mp (Eq.symm h)
    simp [this]
  · refine' (mul_le_mul_right h).mp _
    calc
      ‖x‖ * ‖x‖ = ‖x‖ ^ 2 := by ring
      _ = re ⟪x, x⟫ := norm_sq_eq_inner _
      _ ≤ abs ⟪x, x⟫ := re_le_abs _
      _ = ‖innerSL x x‖ := by
        rw [← IsROrC.norm_eq_abs]
        rfl
      _ ≤ ‖innerSL x‖ * ‖x‖ := (innerSL x : E →L[𝕜] 𝕜).le_op_norm _
      
#align innerSL_apply_norm innerSL_apply_norm

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    innerSL
#align innerSL_flip innerSLFlip

@[simp]
theorem innerSLFlip_apply {x y : E} : innerSLFlip x y = ⟪y, x⟫ :=
  rfl
#align innerSL_flip_apply innerSLFlip_apply

namespace ContinuousLinearMap

variable {E' : Type _} [InnerProductSpace 𝕜 E']

/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `λ x y, ⟪x, A y⟫`, given
as a continuous linear map. -/
def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  ↑(ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) innerSLFlip
#align continuous_linear_map.to_sesq_form ContinuousLinearMap.toSesqForm

@[simp]
theorem toSesqForm_apply_coe (f : E →L[𝕜] E') (x : E') : toSesqForm f x = (innerSL x).comp f :=
  rfl
#align continuous_linear_map.to_sesq_form_apply_coe ContinuousLinearMap.toSesqForm_apply_coe

theorem toSesqForm_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ ≤ ‖f‖ * ‖v‖ :=
  by
  refine' op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  intro x
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖ := h₂
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring
    
#align continuous_linear_map.to_sesq_form_apply_norm_le ContinuousLinearMap.toSesqForm_apply_norm_le

end ContinuousLinearMap

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `is_bounded_bilinear_map`.

In order to state these results, we need a `normed_space ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `inner_product_space.is_R_or_C_to_real 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[normed_space ℝ E]`.
-/
theorem isBoundedBilinearMapInner [NormedSpace ℝ E] :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := fun _ _ _ => inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebra_map_eq_of_real, inner_smul_real_left]
    add_right := fun _ _ _ => inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebra_map_eq_of_real, inner_smul_real_right]
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mul]
        exact norm_inner_le_norm x y⟩ }
#align is_bounded_bilinear_map_inner isBoundedBilinearMapInner

end Norm

section BesselsInequality

variable {ι : Type _} (x : E) {v : ι → E}

/-- Bessel's inequality for finite sums. -/
theorem Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal 𝕜 v) :
    (∑ i in s, ‖⟪v i, x⟫‖ ^ 2) ≤ ‖x‖ ^ 2 :=
  by
  have h₂ :
    (∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k in s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) :=
    hv.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, re (z * conj z) = ‖z‖ ^ 2 :=
    by
    intro z
    simp only [mul_conj, norm_sq_eq_def']
    norm_cast
  suffices hbf : ‖x - ∑ i in s, ⟪v i, x⟫ • v i‖ ^ 2 = ‖x‖ ^ 2 - ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  · rw [← sub_nonneg, ← hbf]
    simp only [norm_nonneg, pow_nonneg]
  rw [norm_sub_sq, sub_add]
  simp only [InnerProductSpace.norm_sq_eq_inner, inner_sum]
  simp only [sum_inner, two_mul, inner_smul_right, inner_conj_sym, ← mul_assoc, h₂, ← h₃,
    inner_conj_sym, AddMonoidHom.map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, inner_smul_left,
    add_sub_cancel']
#align orthonormal.sum_inner_products_le Orthonormal.sum_inner_products_le

/-- Bessel's inequality. -/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) :
    (∑' i, ‖⟪v i, x⟫‖ ^ 2) ≤ ‖x‖ ^ 2 :=
  by
  refine' tsum_le_of_sum_le' _ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]
#align orthonormal.tsum_inner_products_le Orthonormal.tsum_inner_products_le

/-- The sum defined in Bessel's inequality is summable. -/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) :
    Summable fun i => ‖⟪v i, x⟫‖ ^ 2 :=
  by
  use ⨆ s : Finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine' isLUB_csupᵢ _
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x
#align orthonormal.inner_products_summable Orthonormal.inner_products_summable

end BesselsInequality

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance IsROrC.innerProductSpace : InnerProductSpace 𝕜 𝕜
    where
  toNormedAddCommGroup := NonUnitalNormedRing.toNormedAddCommGroup
  inner x y := conj x * y
  norm_sq_eq_inner x := by
    unfold inner
    rw [mul_comm, mul_conj, of_real_re, norm_sq_eq_def']
  conj_sym x y := by simp only [mul_comm, map_mul, starRingEnd_self_apply]
  add_left x y z := by simp only [add_mul, map_add]
  smul_left x y z := by simp only [mul_assoc, smul_eq_mul, map_mul]
#align is_R_or_C.inner_product_space IsROrC.innerProductSpace

@[simp]
theorem IsROrC.inner_apply (x y : 𝕜) : ⟪x, y⟫ = conj x * y :=
  rfl
#align is_R_or_C.inner_apply IsROrC.inner_apply

/-! ### Inner product space structure on subspaces -/


/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  {
    Submodule.normedSpace
      W with
    toNormedAddCommGroup := Submodule.normedAddCommGroup _
    inner := fun x y => ⟪(x : E), (y : E)⟫
    conj_sym := fun _ _ => inner_conj_sym _ _
    norm_sq_eq_inner := fun _ => norm_sq_eq_inner _
    add_left := fun _ _ _ => inner_add_left
    smul_left := fun _ _ _ => inner_smul_left }
#align submodule.inner_product_space Submodule.innerProductSpace

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl
#align submodule.coe_inner Submodule.coe_inner

theorem Orthonormal.codRestrict {ι : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
    (hvs : ∀ i, v i ∈ s) : @Orthonormal 𝕜 s _ _ ι (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv
#align orthonormal.cod_restrict Orthonormal.codRestrict

theorem orthonormalSpan {ι : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) :
    @Orthonormal 𝕜 (Submodule.span 𝕜 (Set.range v)) _ _ ι fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)
#align orthonormal_span orthonormalSpan

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/


section OrthogonalFamily

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

open DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → submodule 𝕜 E`.  We
We instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`pi_lp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def OrthogonalFamily {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) :
    Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0
#align orthogonal_family OrthogonalFamily

variable {𝕜} {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)] {V : ∀ i, G i →ₗᵢ[𝕜] E}
  (hV : OrthogonalFamily 𝕜 V) [dec_V : ∀ (i) (x : G i), Decidable (x ≠ 0)]

theorem Orthonormal.orthogonalFamily {v : ι → E} (hv : Orthonormal 𝕜 v) :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun i : ι => 𝕜) _ fun i =>
      LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]
#align orthonormal.orthogonal_family Orthonormal.orthogonalFamily

include hV dec_ι

theorem OrthogonalFamily.eq_ite {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 :=
  by
  split_ifs
  · rfl
  · exact hV h v w
#align orthogonal_family.eq_ite OrthogonalFamily.eq_ite

include dec_V

theorem OrthogonalFamily.inner_right_dfinsupp (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.Sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.Sum fun j => V j⟫ = l.Sum fun j => fun w => ⟪V i v, V j w⟫ :=
      Dfinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.Sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      congr_arg l.Sum <| funext fun j => funext <| hV.eq_ite v
    _ = ⟪v, l i⟫ :=
      by
      simp only [Dfinsupp.sum, Submodule.coe_inner, Finset.sum_ite_eq, ite_eq_left_iff,
        Dfinsupp.mem_support_toFun]
      split_ifs with h h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]
    
#align orthogonal_family.inner_right_dfinsupp OrthogonalFamily.inner_right_dfinsupp

omit dec_ι dec_V

theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical calc
      ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
      _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
        congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j)
      _ = ⟪v, l i⟫ := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]
      
#align orthogonal_family.inner_right_fintype OrthogonalFamily.inner_right_fintype

theorem OrthogonalFamily.inner_sum (l₁ l₂ : ∀ i, G i) (s : Finset ι) :
    ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
  classical calc
      ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ j in s, ∑ i in s, ⟪V i (l₁ i), V j (l₂ j)⟫ :=
        by simp only [sum_inner, inner_sum]
      _ = ∑ j in s, ∑ i in s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 :=
        by
        congr with i
        congr with j
        apply hV.eq_ite
      _ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
        simp only [Finset.sum_ite_of_true, Finset.sum_ite_eq', LinearIsometry.inner_map_map,
          imp_self, imp_true_iff]
      
#align orthogonal_family.inner_sum OrthogonalFamily.inner_sum

theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) :
    ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2 :=
  by
  have : (‖∑ i in s, V i (l i)‖ ^ 2 : 𝕜) = ∑ i in s, ‖l i‖ ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact_mod_cast this
#align orthogonal_family.norm_sum OrthogonalFamily.norm_sum

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp {γ : Type _} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 fun g : γ => (V (f g) : G (f g) →ₗᵢ[𝕜] E) := fun i j hij v w =>
  hV (hf.Ne hij) v w
#align orthogonal_family.comp OrthogonalFamily.comp

theorem OrthogonalFamily.orthonormalSigmaOrthonormal {α : ι → Type _} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σi, α i => V a.1 (v_family a.1 a.2) :=
  by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v ≠ w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)
#align orthogonal_family.orthonormal_sigma_orthonormal OrthogonalFamily.orthonormalSigmaOrthonormal

include dec_ι

theorem OrthogonalFamily.norm_sq_diff_sum (f : ∀ i, G i) (s₁ s₂ : Finset ι) :
    ‖(∑ i in s₁, V i (f i)) - ∑ i in s₂, V i (f i)‖ ^ 2 =
      (∑ i in s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 :=
  by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  let F : ∀ i, G i := fun i => if i ∈ s₁ then f i else -f i
  have hF₁ : ∀ i ∈ s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset _ _ hi)
  have hF₂ : ∀ i ∈ s₂ \ s₁, F i = -f i := fun i hi => if_neg (finset.mem_sdiff.mp hi).2
  have hF : ∀ i, ‖F i‖ = ‖f i‖ := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [eq_self_iff_true, norm_neg]
  have :
    ‖(∑ i in s₁ \ s₂, V i (F i)) + ∑ i in s₂ \ s₁, V i (F i)‖ ^ 2 =
      (∑ i in s₁ \ s₂, ‖F i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖F i‖ ^ 2 :=
    by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁)
  convert this using 4
  · refine' Finset.sum_congr rfl fun i hi => _
    simp only [hF₁ i hi]
  · refine' Finset.sum_congr rfl fun i hi => _
    simp only [hF₂ i hi, LinearIsometry.map_neg]
  · simp only [hF]
  · simp only [hF]
#align orthogonal_family.norm_sq_diff_sum OrthogonalFamily.norm_sq_diff_sum

omit dec_ι

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ‖f i‖ ^ 2)` is summable. -/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : ∀ i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
      refine' (_root_.abs_sub _ _).trans_lt _
      have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i in s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2) < sqrt ε ^ 2 :=
        by
        rw [← hV.norm_sq_diff_sum, sq_lt_sq, _root_.abs_of_nonneg (sqrt_nonneg _),
          _root_.abs_of_nonneg (norm_nonneg _)]
        exact H s₁ hs₁ s₂ hs₂
      have hη := sq_sqrt (le_of_lt hε)
      linarith
    · intro hf ε hε
      have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
      obtain ⟨a, H⟩ := hf _ hε'
      use a
      intro s₁ hs₁ s₂ hs₂
      refine' (abs_lt_of_sq_lt_sq' _ (le_of_lt hε)).2
      have has : a ≤ s₁ ⊓ s₂ := le_inf hs₁ hs₂
      rw [hV.norm_sq_diff_sum]
      have Hs₁ : (∑ x : ι in s₁ \ s₂, ‖f x‖ ^ 2) < ε ^ 2 / 2 :=
        by
        convert H _ hs₁ _ has
        have : s₁ ⊓ s₂ ⊆ s₁ := Finset.inter_subset_left _ _
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      have Hs₂ : (∑ x : ι in s₂ \ s₁, ‖f x‖ ^ 2) < ε ^ 2 / 2 :=
        by
        convert H _ hs₂ _ has
        have : s₁ ⊓ s₂ ⊆ s₂ := Finset.inter_subset_right _ _
        rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      linarith
#align orthogonal_family.summable_iff_norm_sq_summable OrthogonalFamily.summable_iff_norm_sq_summable

omit hV

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem OrthogonalFamily.independent {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
    CompleteLattice.Independent V := by
  classical
    apply CompleteLattice.independent_of_dfinsupp_lsum_injective
    rw [← @LinearMap.ker_eq_bot _ _ _ _ _ _ (DirectSum.addCommGroup fun i => V i),
      Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    ext i
    suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using this
    calc
      ⟪(v i : E), v i⟫ = ⟪(v i : E), Dfinsupp.lsum ℕ (fun i => (V i).Subtype) v⟫ := by
        simpa only [Dfinsupp.sumAddHom_apply, Dfinsupp.lsum_apply_apply] using
          (hV.inner_right_dfinsupp v i (v i)).symm
      _ = 0 := by simp only [hv, inner_zero_right]
      
#align orthogonal_family.independent OrthogonalFamily.independent

include dec_ι

theorem DirectSum.IsInternal.collectedBasisOrthonormal {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type _}
    {v_family : ∀ i, Basis (α i) 𝕜 (V i)} (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collected_basis_coe] using hV.orthonormal_sigma_orthonormal hv_family
#align direct_sum.is_internal.collected_basis_orthonormal DirectSum.IsInternal.collectedBasisOrthonormal

end OrthogonalFamily

section IsROrCToReal

variable {G : Type _}

variable (𝕜 E)

include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def HasInner.isROrCToReal : HasInner ℝ E where inner x y := re ⟪x, y⟫
#align has_inner.is_R_or_C_to_real HasInner.isROrCToReal

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def InnerProductSpace.isROrCToReal : InnerProductSpace ℝ E :=
  { HasInner.isROrCToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜
      E with
    toNormedAddCommGroup := InnerProductSpace.toNormedAddCommGroup 𝕜
    norm_sq_eq_inner := norm_sq_eq_inner
    conj_sym := fun x y => inner_re_symm
    add_left := fun x y z => by
      change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫
      simp only [inner_add_left, map_add]
    smul_left := fun x y r => by
      change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫
      simp only [inner_smul_left, conj_of_real, of_real_mul_re] }
#align inner_product_space.is_R_or_C_to_real InnerProductSpace.isROrCToReal

variable {E}

theorem real_inner_eq_re_inner (x y : E) :
    @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x y = re ⟪x, y⟫ :=
  rfl
#align real_inner_eq_re_inner real_inner_eq_re_inner

theorem real_inner_i_smul_self (x : E) :
    @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x ((i : 𝕜) • x) = 0 := by
  simp [real_inner_eq_re_inner, inner_smul_right]
#align real_inner_I_smul_self real_inner_i_smul_self

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance InnerProductSpace.complexToReal [InnerProductSpace ℂ G] : InnerProductSpace ℝ G :=
  InnerProductSpace.isROrCToReal ℂ G
#align inner_product_space.complex_to_real InnerProductSpace.complexToReal

@[simp]
protected theorem Complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (conj w * z).re :=
  rfl
#align complex.inner Complex.inner

/-- The inner product on an inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem inner_map_complex [InnerProductSpace ℝ G] (f : G ≃ₗᵢ[ℝ] ℂ) (x y : G) :
    ⟪x, y⟫_ℝ = (conj (f x) * f y).re := by rw [← Complex.inner, f.inner_map_map]
#align inner_map_complex inner_map_complex

end IsROrCToReal

section Continuous

/-!
### Continuity of the inner product
-/


theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  is_bounded_bilinear_map_inner.continuous
#align continuous_inner continuous_inner

variable {α : Type _}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.Tendsto _).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.inner Filter.Tendsto.inner

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

include 𝕜

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  hf.inner hg
#align continuous_within_at.inner ContinuousWithinAt.inner

theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  hf.inner hg
#align continuous_at.inner ContinuousAt.inner

theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)
#align continuous_on.inner ContinuousOn.inner

@[continuity]
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.inner hg.ContinuousAt
#align continuous.inner Continuous.inner

end Continuous

section ReApplyInnerSelf

/-- Extract a real bilinear form from an operator `T`, by taking the pairing `λ x, re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫
#align continuous_linear_map.re_apply_inner_self ContinuousLinearMap.reApplyInnerSelf

theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E →L[𝕜] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl
#align continuous_linear_map.re_apply_inner_self_apply ContinuousLinearMap.reApplyInnerSelf_apply

theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[𝕜] E) :
    Continuous T.reApplyInnerSelf :=
  reClm.Continuous.comp <| T.Continuous.inner continuous_id
#align continuous_linear_map.re_apply_inner_self_continuous ContinuousLinearMap.reApplyInnerSelf_continuous

theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_smul_left, inner_smul_right, ← mul_assoc, mul_conj, norm_sq_eq_def', ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebra_map_eq_of_real]
#align continuous_linear_map.re_apply_inner_self_smul ContinuousLinearMap.reApplyInnerSelf_smul

end ReApplyInnerSelf

/-! ### The orthogonal complement -/


section Orthogonal

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def Submodule.orthogonal : Submodule 𝕜 E
    where
  carrier := { v | ∀ u ∈ K, ⟪u, v⟫ = 0 }
  zero_mem' _ _ := inner_zero_right
  add_mem' x y hx hy u hu := by rw [inner_add_right, hx u hu, hy u hu, add_zero]
  smul_mem' c x hx u hu := by rw [inner_smul_right, hx u hu, mul_zero]
#align submodule.orthogonal Submodule.orthogonal

-- mathport name: «expr ᗮ»
notation:1200 K "ᗮ" => Submodule.orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem Submodule.mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl
#align submodule.mem_orthogonal Submodule.mem_orthogonal

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem Submodule.mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u ∈ K, ⟪v, u⟫ = 0 := by
  simp_rw [Submodule.mem_orthogonal, inner_eq_zero_sym]
#align submodule.mem_orthogonal' Submodule.mem_orthogonal'

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem Submodule.inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu
#align submodule.inner_right_of_mem_orthogonal Submodule.inner_right_of_mem_orthogonal

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem Submodule.inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 :=
  by rw [inner_eq_zero_sym] <;> exact Submodule.inner_right_of_mem_orthogonal hu hv
#align submodule.inner_left_of_mem_orthogonal Submodule.inner_left_of_mem_orthogonal

/-- A vector is in `(𝕜 ∙ u)ᗮ` iff it is orthogonal to `u`. -/
theorem Submodule.mem_orthogonal_singleton_iff_inner_right {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪u, v⟫ = 0 :=
  by
  refine' ⟨Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u), _⟩
  intro hv w hw
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [inner_smul_left, hv]
#align submodule.mem_orthogonal_singleton_iff_inner_right Submodule.mem_orthogonal_singleton_iff_inner_right

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem Submodule.mem_orthogonal_singleton_iff_inner_left {u v : E} : v ∈ (𝕜 ∙ u)ᗮ ↔ ⟪v, u⟫ = 0 :=
  by rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_eq_zero_sym]
#align submodule.mem_orthogonal_singleton_iff_inner_left Submodule.mem_orthogonal_singleton_iff_inner_left

theorem Submodule.sub_mem_orthogonal_of_inner_left {x y : E} (h : ∀ v : K, ⟪x, v⟫ = ⟪y, v⟫) :
    x - y ∈ Kᗮ := by
  rw [Submodule.mem_orthogonal']
  intro u hu
  rw [inner_sub_left, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_left Submodule.sub_mem_orthogonal_of_inner_left

theorem Submodule.sub_mem_orthogonal_of_inner_right {x y : E}
    (h : ∀ v : K, ⟪(v : E), x⟫ = ⟪(v : E), y⟫) : x - y ∈ Kᗮ :=
  by
  intro u hu
  rw [inner_sub_right, sub_eq_zero]
  exact h ⟨u, hu⟩
#align submodule.sub_mem_orthogonal_of_inner_right Submodule.sub_mem_orthogonal_of_inner_right

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.inf_orthogonal_eq_bot : K ⊓ Kᗮ = ⊥ :=
  by
  rw [Submodule.eq_bot_iff]
  intro x
  rw [Submodule.mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)
#align submodule.inf_orthogonal_eq_bot Submodule.inf_orthogonal_eq_bot

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.orthogonal_disjoint : Disjoint K Kᗮ := by
  simp [disjoint_iff, K.inf_orthogonal_eq_bot]
#align submodule.orthogonal_disjoint Submodule.orthogonal_disjoint

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, LinearMap.ker (innerSL (v : E) : E →L[𝕜] 𝕜) :=
  by
  apply le_antisymm
  · rw [le_infᵢ_iff]
    rintro ⟨v, hv⟩ w hw
    simpa using hw _ hv
  · intro v hv w hw
    simp only [Submodule.mem_infᵢ] at hv
    exact hv ⟨w, hw⟩
#align orthogonal_eq_inter orthogonal_eq_inter

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem Submodule.isClosed_orthogonal : IsClosed (Kᗮ : Set E) :=
  by
  rw [orthogonal_eq_inter K]
  have := fun v : K => ContinuousLinearMap.isClosed_ker (innerSL (v : E) : E →L[𝕜] 𝕜)
  convert isClosed_interᵢ this
  simp only [Submodule.infᵢ_coe]
#align submodule.is_closed_orthogonal Submodule.isClosed_orthogonal

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.isClosed_orthogonal.completeSpace_coe

variable (𝕜 E)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem Submodule.orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ Submodule.orthogonal
      Submodule.orthogonal :=
  fun K₁ K₂ =>
  ⟨fun h v hv u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h v hv u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩
#align submodule.orthogonal_gc Submodule.orthogonal_gc

variable {𝕜 E}

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).monotone_l h
#align submodule.orthogonal_le Submodule.orthogonal_le

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) :
    K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  Submodule.orthogonal_le (Submodule.orthogonal_le h)
#align submodule.orthogonal_orthogonal_monotone Submodule.orthogonal_orthogonal_monotone

/-- `K` is contained in `Kᗮᗮ`. -/
theorem Submodule.le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).le_u_l _
#align submodule.le_orthogonal_orthogonal Submodule.le_orthogonal_orthogonal

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem Submodule.inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ ⊓ K₂ᗮ = (K₁ ⊔ K₂)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_sup.symm
#align submodule.inf_orthogonal Submodule.inf_orthogonal

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem Submodule.infᵢ_orthogonal {ι : Type _} (K : ι → Submodule 𝕜 E) :
    (⨅ i, (K i)ᗮ) = (supᵢ K)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_supᵢ.symm
#align submodule.infi_orthogonal Submodule.infᵢ_orthogonal

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem Submodule.Inf_orthogonal (s : Set <| Submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (supₛ s)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_supₛ.symm
#align submodule.Inf_orthogonal Submodule.Inf_orthogonal

@[simp]
theorem Submodule.top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ :=
  by
  ext
  rw [Submodule.mem_bot, Submodule.mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x Submodule.mem_top),
      by
      rintro rfl
      simp⟩
#align submodule.top_orthogonal_eq_bot Submodule.top_orthogonal_eq_bot

@[simp]
theorem Submodule.bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ :=
  by
  rw [← Submodule.top_orthogonal_eq_bot, eq_top_iff]
  exact Submodule.le_orthogonal_orthogonal ⊤
#align submodule.bot_orthogonal_eq_top Submodule.bot_orthogonal_eq_top

@[simp]
theorem Submodule.orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ :=
  by
  refine'
    ⟨_, by
      rintro rfl
      exact Submodule.bot_orthogonal_eq_top⟩
  intro h
  have : K ⊓ Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this
#align submodule.orthogonal_eq_top_iff Submodule.orthogonal_eq_top_iff

theorem Submodule.orthogonalFamilySelf :
    @OrthogonalFamily 𝕜 E _ _ _ (fun b => ((cond b K Kᗮ : Submodule 𝕜 E) : Type _)) _ fun b =>
      (cond b K Kᗮ).subtypeₗᵢ
  | tt, tt => absurd rfl
  | tt, ff => fun _ x y => Submodule.inner_right_of_mem_orthogonal x.Prop y.Prop
  | ff, tt => fun _ x y => Submodule.inner_left_of_mem_orthogonal y.Prop x.Prop
  | ff, ff => absurd rfl
#align submodule.orthogonal_family_self Submodule.orthogonalFamilySelf

end Orthogonal

namespace UniformSpace.Completion

open UniformSpace Function

instance {𝕜' E' : Type _} [TopologicalSpace 𝕜'] [UniformSpace E'] [HasInner 𝕜' E'] :
    HasInner 𝕜' (Completion E')
    where inner := curry <| (denseInducing_coe.Prod denseInducing_coe).extend (uncurry inner)

@[simp]
theorem inner_coe (a b : E) : inner (a : Completion E) (b : Completion E) = (inner a b : 𝕜) :=
  (denseInducing_coe.Prod denseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry inner : E × E → 𝕜)) (a, b)
#align uniform_space.completion.inner_coe UniformSpace.Completion.inner_coe

protected theorem continuous_inner : Continuous (uncurry inner : Completion E × Completion E → 𝕜) :=
  by
  let inner' : E →+ E →+ 𝕜 :=
    { toFun := fun x => (innerₛₗ x).toAddMonoidHom
      map_zero' := by ext x <;> exact inner_zero_left
      map_add' := fun x y => by ext z <;> exact inner_add_left }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [completion.has_inner, uncurry_curry _]
  change
    Continuous
      (((dense_inducing_to_compl E).Prod (dense_inducing_to_compl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (dense_inducing_to_compl E).extend_Z_bilin (dense_inducing_to_compl E) this
#align uniform_space.completion.continuous_inner UniformSpace.Completion.continuous_inner

protected theorem Continuous.inner {α : Type _} [TopologicalSpace α] {f g : α → Completion E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x : α => inner (f x) (g x) : α → 𝕜) :=
  UniformSpace.Completion.continuous_inner.comp (hf.prod_mk hg : _)
#align uniform_space.completion.continuous.inner UniformSpace.Completion.Continuous.inner

instance : InnerProductSpace 𝕜 (Completion E)
    where
  toNormedAddCommGroup := inferInstance
  norm_sq_eq_inner x :=
    Completion.induction_on x
      (isClosed_eq (continuous_norm.pow 2)
        (continuous_re.comp (Continuous.inner continuous_id' continuous_id')))
      fun a => by simp only [norm_coe, inner_coe, inner_self_eq_norm_sq]
  conj_sym x y :=
    Completion.induction_on₂ x y
      (isClosed_eq (continuous_conj.comp (Continuous.inner continuous_snd continuous_fst))
        (Continuous.inner continuous_fst continuous_snd))
      fun a b => by simp only [inner_coe, inner_conj_sym]
  add_left x y z :=
    Completion.induction_on₃ x y z
      (isClosed_eq
        (Continuous.inner (continuous_fst.add (continuous_fst.comp continuous_snd))
          (continuous_snd.comp continuous_snd))
        ((Continuous.inner continuous_fst (continuous_snd.comp continuous_snd)).add
          (Continuous.inner (continuous_fst.comp continuous_snd)
            (continuous_snd.comp continuous_snd))))
      fun a b c => by simp only [← coe_add, inner_coe, inner_add_left]
  smul_left x y c :=
    Completion.induction_on₂ x y
      (isClosed_eq (Continuous.inner (continuous_fst.const_smul c) continuous_snd)
        ((continuous_mul_left _).comp (Continuous.inner continuous_fst continuous_snd)))
      fun a b => by simp only [← coe_smul c a, inner_coe, inner_smul_left]

end UniformSpace.Completion

