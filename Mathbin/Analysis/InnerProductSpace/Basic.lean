import Mathbin.Algebra.DirectSum.Module 
import Mathbin.Analysis.Complex.Basic 
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps 
import Mathbin.LinearAlgebra.BilinearForm 
import Mathbin.LinearAlgebra.SesquilinearForm

/-!
# Inner product space

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the pair of assumptions
`[inner_product_space E] [complete_space E]`.

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
- We show that the inner product is continuous, `continuous_inner`.
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


noncomputable theory

open IsROrC Real Filter

open_locale BigOperators Classical TopologicalSpace ComplexConjugate

variable {𝕜 E F : Type _} [IsROrC 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class HasInner (𝕜 E : Type _) where 
  inner : E → E → 𝕜

export HasInner(inner)

notation "⟪" x ", " y "⟫_ℝ" => @inner ℝ _ _ x y

notation "⟪" x ", " y "⟫_ℂ" => @inner ℂ _ _ x y

section Notations

localized [RealInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

localized [ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

end Notations

/--
An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `∥x∥^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class InnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] extends NormedGroup E, NormedSpace 𝕜 E, HasInner 𝕜 E where 
  norm_sq_eq_inner : ∀ x : E, (∥x∥^2) = re (inner x x)
  conj_sym : ∀ x y, conj (inner y x) = inner x y 
  add_left : ∀ x y z, inner (x+y) z = inner x z+inner y z 
  smulLeft : ∀ x y r, inner (r • x) y = conj r*inner x y

attribute [nolint dangerous_instance] InnerProductSpace.toNormedGroup

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


/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_inhabited_instance]
structure InnerProductSpace.Core (𝕜 : Type _) (F : Type _) [IsROrC 𝕜] [AddCommGroupₓ F] [Module 𝕜 F] where 
  inner : F → F → 𝕜 
  conj_sym : ∀ x y, conj (inner y x) = inner x y 
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  definite : ∀ x, inner x x = 0 → x = 0
  add_left : ∀ x y z, inner (x+y) z = inner x z+inner y z 
  smulLeft : ∀ x y r, inner (r • x) y = conj r*inner x y

attribute [class] InnerProductSpace.Core

namespace InnerProductSpace.ofCore

variable [AddCommGroupₓ F] [Module 𝕜 F] [c : InnerProductSpace.Core 𝕜 F]

include c

local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

local notation "norm_sqK" => @IsROrC.normSq 𝕜 _

local notation "reK" => @IsROrC.re 𝕜 _

local notation "absK" => @IsROrC.abs 𝕜 _

local notation "ext_iff" => @IsROrC.ext_iff 𝕜 _

local postfix:90 "†" => starRingAut

/-- Inner product defined by the `inner_product_space.core` structure. -/
def to_has_inner : HasInner 𝕜 F :=
  { inner := c.inner }

attribute [local instance] to_has_inner

/-- The norm squared function for `inner_product_space.core` structure. -/
def norm_sq (x : F) :=
  reK ⟪x, x⟫

local notation "norm_sqF" => @norm_sq 𝕜 F _ _ _ _

theorem inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_sym x y

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _

theorem inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 :=
  by 
    rw [←@of_real_inj 𝕜, im_eq_conj_sub] <;> simp [inner_conj_sym]

theorem inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im

theorem inner_add_left {x y z : F} : ⟪x+y, z⟫ = ⟪x, z⟫+⟪y, z⟫ :=
  c.add_left _ _ _

theorem inner_add_right {x y z : F} : ⟪x, y+z⟫ = ⟪x, y⟫+⟪x, z⟫ :=
  by 
    rw [←inner_conj_sym, inner_add_left, RingEquiv.map_add] <;> simp only [inner_conj_sym]

theorem inner_norm_sq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ :=
  by 
    rw [ext_iff]
    exact
      ⟨by 
          simp only [of_real_re] <;> rfl,
        by 
          simp only [inner_self_nonneg_im, of_real_im]⟩

theorem inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, conj_re]

theorem inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, conj_im]

theorem inner_smul_left {x y : F} {r : 𝕜} : ⟪r • x, y⟫ = r†*⟪x, y⟫ :=
  c.smul_left _ _ _

theorem inner_smul_right {x y : F} {r : 𝕜} : ⟪x, r • y⟫ = r*⟪x, y⟫ :=
  by 
    rw [←inner_conj_sym, inner_smul_left] <;> simp only [conj_conj, inner_conj_sym, RingEquiv.map_mul]

theorem inner_zero_left {x : F} : ⟪0, x⟫ = 0 :=
  by 
    rw [←zero_smul 𝕜 (0 : F), inner_smul_left] <;> simp only [zero_mul, RingEquiv.map_zero]

theorem inner_zero_right {x : F} : ⟪x, 0⟫ = 0 :=
  by 
    rw [←inner_conj_sym, inner_zero_left] <;> simp only [RingEquiv.map_zero]

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  Iff.intro (c.definite _)
    (by 
      rintro rfl 
      exact inner_zero_left)

theorem inner_self_re_to_K {x : F} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  by 
    normNum [ext_iff, inner_self_nonneg_im]

theorem inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, abs_conj]

theorem inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ :=
  by 
    rw [←neg_one_smul 𝕜 x, inner_smul_left]
    simp 

theorem inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ :=
  by 
    rw [←inner_conj_sym, inner_neg_left] <;> simp only [RingEquiv.map_neg, inner_conj_sym]

theorem inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
  by 
    simp [sub_eq_add_neg, inner_add_left, inner_neg_left]

theorem inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
  by 
    simp [sub_eq_add_neg, inner_add_right, inner_neg_right]

theorem inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫*⟪y, x⟫) = abs (⟪x, y⟫*⟪y, x⟫) :=
  by 
    rw [←inner_conj_sym, mul_commₓ]
    exact re_eq_abs_of_mul_conj (inner y x)

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self {x y : F} : ⟪x+y, x+y⟫ = ((⟪x, x⟫+⟪x, y⟫)+⟪y, x⟫)+⟪y, y⟫ :=
  by 
    simp only [inner_add_left, inner_add_right] <;> ring

theorem inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫)+⟪y, y⟫ :=
  by 
    simp only [inner_sub_left, inner_sub_right] <;> ring

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
**Cauchy–Schwarz inequality**. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le
(x
 y : F) : «expr ≤ »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), «expr * »(re «expr⟪ , ⟫»(x, x), re «expr⟪ , ⟫»(y, y))) :=
begin
  by_cases [expr hy, ":", expr «expr = »(y, 0)],
  { rw ["[", expr hy, "]"] [],
    simp [] [] ["only"] ["[", expr is_R_or_C.abs_zero, ",", expr inner_zero_left, ",", expr mul_zero, ",", expr add_monoid_hom.map_zero, "]"] [] [] },
  { change [expr «expr ≠ »(y, 0)] [] ["at", ident hy],
    have [ident hy'] [":", expr «expr ≠ »(«expr⟪ , ⟫»(y, y), 0)] [":=", expr λ
     h, by rw ["[", expr inner_self_eq_zero, "]"] ["at", ident h]; exact [expr hy h]],
    set [] [ident T] [] [":="] [expr «expr / »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(y, y))] ["with", ident hT],
    have [ident h₁] [":", expr «expr = »(re «expr⟪ , ⟫»(y, x), re «expr⟪ , ⟫»(x, y))] [":=", expr inner_re_symm],
    have [ident h₂] [":", expr «expr = »(im «expr⟪ , ⟫»(y, x), «expr- »(im «expr⟪ , ⟫»(x, y)))] [":=", expr inner_im_symm],
    have [ident h₃] [":", expr «expr = »(«expr / »(«expr * »(«expr * »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(x, y)), «expr⟪ , ⟫»(y, y)), «expr * »(«expr⟪ , ⟫»(y, y), «expr⟪ , ⟫»(y, y))), «expr / »(«expr * »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(x, y)), «expr⟪ , ⟫»(y, y)))] [],
    { rw ["[", expr mul_div_assoc, "]"] [],
      have [] [":", expr «expr = »(«expr / »(«expr⟪ , ⟫»(y, y), «expr * »(«expr⟪ , ⟫»(y, y), «expr⟪ , ⟫»(y, y))), «expr / »(1, «expr⟪ , ⟫»(y, y)))] [":=", expr by rw ["[", expr div_mul_eq_div_mul_one_div, ",", expr div_self hy', ",", expr one_mul, "]"] []],
      rw ["[", expr this, ",", expr div_eq_mul_inv, ",", expr one_mul, ",", "<-", expr div_eq_mul_inv, "]"] [] },
    have [ident h₄] [":", expr «expr = »(«expr⟪ , ⟫»(y, y), re «expr⟪ , ⟫»(y, y))] [":=", expr by simp [] [] ["only"] ["[", expr inner_self_re_to_K, "]"] [] []],
    have [ident h₅] [":", expr «expr > »(re «expr⟪ , ⟫»(y, y), 0)] [],
    { refine [expr lt_of_le_of_ne inner_self_nonneg _],
      intro [ident H],
      apply [expr hy'],
      rw [expr exprext_iff()] [],
      exact [expr ⟨by simp [] [] ["only"] ["[", expr H, ",", expr zero_re', "]"] [] [], by simp [] [] ["only"] ["[", expr inner_self_nonneg_im, ",", expr add_monoid_hom.map_zero, "]"] [] []⟩] },
    have [ident h₆] [":", expr «expr ≠ »(re «expr⟪ , ⟫»(y, y), 0)] [":=", expr ne_of_gt h₅],
    have [ident hmain] [] [":=", expr calc
       «expr ≤ »(0, re «expr⟪ , ⟫»(«expr - »(x, «expr • »(T, y)), «expr - »(x, «expr • »(T, y)))) : inner_self_nonneg
       «expr = »(..., «expr + »(«expr - »(«expr - »(re «expr⟪ , ⟫»(x, x), re «expr⟪ , ⟫»(«expr • »(T, y), x)), re «expr⟪ , ⟫»(x, «expr • »(T, y))), re «expr⟪ , ⟫»(«expr • »(T, y), «expr • »(T, y)))) : by simp [] [] ["only"] ["[", expr inner_sub_sub_self, ",", expr inner_smul_left, ",", expr inner_smul_right, ",", expr h₁, ",", expr h₂, ",", expr neg_mul_eq_neg_mul_symm, ",", expr add_monoid_hom.map_add, ",", expr mul_re, ",", expr conj_im, ",", expr add_monoid_hom.map_sub, ",", expr mul_neg_eq_neg_mul_symm, ",", expr conj_re, ",", expr neg_neg, "]"] [] []
       «expr = »(..., «expr + »(«expr - »(«expr - »(re «expr⟪ , ⟫»(x, x), re «expr * »(«expr †»(T), «expr⟪ , ⟫»(y, x))), re «expr * »(T, «expr⟪ , ⟫»(x, y))), re «expr * »(«expr * »(T, «expr †»(T)), «expr⟪ , ⟫»(y, y)))) : by simp [] [] ["only"] ["[", expr inner_smul_left, ",", expr inner_smul_right, ",", expr mul_assoc, "]"] [] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr * »(«expr / »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, y)), «expr⟪ , ⟫»(y, x)))) : by field_simp [] ["[", "-", ident mul_re, ",", expr inner_conj_sym, ",", expr hT, ",", expr ring_equiv.map_div, ",", expr h₁, ",", expr h₃, "]"] [] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr / »(«expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr div_mul_eq_mul_div_comm, ",", "<-", expr mul_div_assoc, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr / »(«expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by conv_lhs [] [] { rw ["[", expr h₄, "]"] }
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(re «expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr div_re_of_real, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(abs «expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr inner_mul_conj_re_abs, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw [expr is_R_or_C.abs_mul] []],
    have [ident hmain'] [":", expr «expr ≤ »(«expr / »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)), re «expr⟪ , ⟫»(x, x))] [":=", expr by linarith [] [] []],
    have [] [] [":=", expr (mul_le_mul_right h₅).mpr hmain'],
    rwa ["[", expr div_mul_cancel «expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)) h₆, "]"] ["at", ident this] }
end

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def to_has_norm : HasNorm F :=
  { norm := fun x => sqrt (re ⟪x, x⟫) }

attribute [local instance] to_has_norm

theorem norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (re ⟪x, x⟫) :=
  rfl

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ∥x∥*∥x∥ :=
  by 
    rw [norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem sqrt_norm_sq_eq_norm {x : F} : sqrt (norm_sqF x) = ∥x∥ :=
  rfl

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : F) : «expr ≤ »(abs «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))) :=
nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) (begin
   have [ident H] [":", expr «expr = »(«expr * »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), «expr * »(re «expr⟪ , ⟫»(y, y), re «expr⟪ , ⟫»(x, x)))] [],
   { simp [] [] ["only"] ["[", expr inner_self_eq_norm_mul_norm, "]"] [] [],
     ring [] },
   rw [expr H] [],
   conv [] [] begin
     to_lhs,
     congr,
     rw ["[", expr inner_abs_conj_sym, "]"]
   end,
   exact [expr inner_mul_inner_self_le y x]
 end)

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def to_normed_group : normed_group F :=
normed_group.of_core F { norm_eq_zero_iff := assume x, begin
    split,
    { intro [ident H],
      change [expr «expr = »(sqrt (re «expr⟪ , ⟫»(x, x)), 0)] [] ["at", ident H],
      rw ["[", expr sqrt_eq_zero inner_self_nonneg, "]"] ["at", ident H],
      apply [expr (inner_self_eq_zero : «expr ↔ »(«expr = »(«expr⟪ , ⟫»(x, x), 0), «expr = »(x, 0))).mp],
      rw [expr exprext_iff()] [],
      exact [expr ⟨by simp [] [] [] ["[", expr H, "]"] [] [], by simp [] [] [] ["[", expr inner_self_im_zero, "]"] [] []⟩] },
    { rintro [ident rfl],
      change [expr «expr = »(sqrt (re «expr⟪ , ⟫»(0, 0)), 0)] [] [],
      simp [] [] ["only"] ["[", expr sqrt_zero, ",", expr inner_zero_right, ",", expr add_monoid_hom.map_zero, "]"] [] [] }
  end,
  triangle := assume x y, begin
    have [ident h₁] [":", expr «expr ≤ »(abs «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)))] [":=", expr abs_inner_le_norm _ _],
    have [ident h₂] [":", expr «expr ≤ »(re «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(x, y))] [":=", expr re_le_abs _],
    have [ident h₃] [":", expr «expr ≤ »(re «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)))] [":=", expr by linarith [] [] []],
    have [ident h₄] [":", expr «expr ≤ »(re «expr⟪ , ⟫»(y, x), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)))] [":=", expr by rwa ["[", "<-", expr inner_conj_sym, ",", expr conj_re, "]"] []],
    have [] [":", expr «expr ≤ »(«expr * »(«expr∥ ∥»(«expr + »(x, y)), «expr∥ ∥»(«expr + »(x, y))), «expr * »(«expr + »(«expr∥ ∥»(x), «expr∥ ∥»(y)), «expr + »(«expr∥ ∥»(x), «expr∥ ∥»(y))))] [],
    { simp [] [] [] ["[", "<-", expr inner_self_eq_norm_mul_norm, ",", expr inner_add_add_self, ",", expr add_mul, ",", expr mul_add, ",", expr mul_comm, "]"] [] [],
      linarith [] [] [] },
    exact [expr nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this]
  end,
  norm_neg := λ
  x, by simp [] [] ["only"] ["[", expr norm, ",", expr inner_neg_left, ",", expr neg_neg, ",", expr inner_neg_right, "]"] [] [] }

attribute [local instance] to_normed_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def to_normed_space : NormedSpace 𝕜 F :=
  { norm_smul_le :=
      fun r x =>
        by 
          rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ←mul_assocₓ]
          rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ←inner_norm_sq_eq_inner_self, of_real_re]
          ·
            simp [sqrt_norm_sq_eq_norm, IsROrC.sqrt_norm_sq_eq_norm]
          ·
            exact norm_sq_nonneg r }

end InnerProductSpace.ofCore

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def inner_product_space.of_core
[add_comm_group F]
[module 𝕜 F]
(c : inner_product_space.core 𝕜 F) : inner_product_space 𝕜 F :=
begin
  letI [] [":", expr normed_group F] [":=", expr @inner_product_space.of_core.to_normed_group 𝕜 F _ _ _ c],
  letI [] [":", expr normed_space 𝕜 F] [":=", expr @inner_product_space.of_core.to_normed_space 𝕜 F _ _ _ c],
  exact [expr { norm_sq_eq_inner := λ x, begin
       have [ident h₁] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(x), 2), «expr ^ »(sqrt (re (c.inner x x)), 2))] [":=", expr rfl],
       have [ident h₂] [":", expr «expr ≤ »(0, re (c.inner x x))] [":=", expr inner_product_space.of_core.inner_self_nonneg],
       simp [] [] [] ["[", expr h₁, ",", expr sq_sqrt, ",", expr h₂, "]"] [] []
     end,
     ..c }]
end

/-! ### Properties of inner product spaces -/


variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

local notation "IK" => @IsROrC.i 𝕜 _

local notation "absR" => HasAbs.abs

local notation "absK" => @IsROrC.abs 𝕜 _

local postfix:90 "†" => starRingAut

export InnerProductSpace(norm_sq_eq_inner)

section BasicProperties

@[simp]
theorem inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_sym _ _

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_sym ℝ _ _ _ x y

theorem inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
  ⟨fun h =>
      by 
        simp [←inner_conj_sym, h],
    fun h =>
      by 
        simp [←inner_conj_sym, h]⟩

@[simp]
theorem inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 :=
  by 
    rw [←@of_real_inj 𝕜, im_eq_conj_sub] <;> simp 

theorem inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im

theorem inner_add_left {x y z : E} : ⟪x+y, z⟫ = ⟪x, z⟫+⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

theorem inner_add_right {x y z : E} : ⟪x, y+z⟫ = ⟪x, y⟫+⟪x, z⟫ :=
  by 
    rw [←inner_conj_sym, inner_add_left, RingEquiv.map_add]
    simp only [inner_conj_sym]

theorem inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, conj_re]

theorem inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, conj_im]

theorem inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r†*⟪x, y⟫ :=
  InnerProductSpace.smul_left _ _ _

theorem real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r*⟪x, y⟫_ℝ :=
  inner_smul_left

theorem inner_smul_real_left {x y : E} {r : ℝ} : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ :=
  by 
    rw [inner_smul_left, conj_of_real, Algebra.smul_def]
    rfl

theorem inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r*⟪x, y⟫ :=
  by 
    rw [←inner_conj_sym, inner_smul_left, RingEquiv.map_mul, conj_conj, inner_conj_sym]

theorem real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r*⟪x, y⟫_ℝ :=
  inner_smul_right

theorem inner_smul_real_right {x y : E} {r : ℝ} : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ :=
  by 
    rw [inner_smul_right, Algebra.smul_def]
    rfl

/-- The inner product as a sesquilinear form. -/
@[simps]
def sesqFormOfInner : SesqForm 𝕜 E (conj_to_ring_equiv 𝕜) :=
  { sesq := fun x y => ⟪y, x⟫, sesq_add_left := fun x y z => inner_add_right,
    sesq_add_right := fun x y z => inner_add_left, sesq_smul_left := fun r x y => inner_smul_right,
    sesq_smul_right := fun r x y => inner_smul_left }

/-- The real inner product as a bilinear form. -/
@[simps]
def bilinFormOfRealInner : BilinForm ℝ F :=
  { bilin := inner, bilin_add_left := fun x y z => inner_add_left, bilin_smul_left := fun a x y => inner_smul_left,
    bilin_add_right := fun x y z => inner_add_right, bilin_smul_right := fun a x y => inner_smul_right }

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) : ⟪∑i in s, f i, x⟫ = ∑i in s, ⟪f i, x⟫ :=
  SesqForm.sum_right sesqFormOfInner _ _ _

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) : ⟪x, ∑i in s, f i⟫ = ∑i in s, ⟪x, f i⟫ :=
  SesqForm.sum_left sesqFormOfInner _ _ _

/-- An inner product with a sum on the left, `finsupp` version. -/
theorem Finsupp.sum_inner {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪l.sum fun i : ι a : 𝕜 => a • v i, x⟫ = l.sum fun i : ι a : 𝕜 => conj a • ⟪v i, x⟫ :=
  by 
    convert sum_inner l.support (fun a => l a • v a) x 
    simp [inner_smul_left, Finsupp.sum]

/-- An inner product with a sum on the right, `finsupp` version. -/
theorem Finsupp.inner_sum {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
  ⟪x, l.sum fun i : ι a : 𝕜 => a • v i⟫ = l.sum fun i : ι a : 𝕜 => a • ⟪x, v i⟫ :=
  by 
    convert inner_sum l.support (fun a => l a • v a) x 
    simp [inner_smul_right, Finsupp.sum]

@[simp]
theorem inner_zero_left {x : E} : ⟪0, x⟫ = 0 :=
  by 
    rw [←zero_smul 𝕜 (0 : E), inner_smul_left, RingEquiv.map_zero, zero_mul]

theorem inner_re_zero_left {x : E} : re ⟪0, x⟫ = 0 :=
  by 
    simp only [inner_zero_left, AddMonoidHom.map_zero]

@[simp]
theorem inner_zero_right {x : E} : ⟪x, 0⟫ = 0 :=
  by 
    rw [←inner_conj_sym, inner_zero_left, RingEquiv.map_zero]

theorem inner_re_zero_right {x : E} : re ⟪x, 0⟫ = 0 :=
  by 
    simp only [inner_zero_right, AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  by 
    rw [←norm_sq_eq_inner] <;> exact pow_nonneg (norm_nonneg x) 2

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ x

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem inner_self_eq_zero {x : E} : «expr ↔ »(«expr = »(«expr⟪ , ⟫»(x, x), 0), «expr = »(x, 0)) :=
begin
  split,
  { intro [ident h],
    have [ident h₁] [":", expr «expr = »(re «expr⟪ , ⟫»(x, x), 0)] [":=", expr by rw [expr is_R_or_C.ext_iff] ["at", ident h]; simp [] [] [] ["[", expr h.1, "]"] [] []],
    rw ["[", "<-", expr norm_sq_eq_inner x, "]"] ["at", ident h₁],
    rw ["[", "<-", expr norm_eq_zero, "]"] [],
    exact [expr pow_eq_zero h₁] },
  { rintro [ident rfl],
    exact [expr inner_zero_left] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp] theorem inner_self_nonpos {x : E} : «expr ↔ »(«expr ≤ »(re «expr⟪ , ⟫»(x, x), 0), «expr = »(x, 0)) :=
begin
  split,
  { intro [ident h],
    rw ["<-", expr inner_self_eq_zero] [],
    have [ident H₁] [":", expr «expr ≥ »(re «expr⟪ , ⟫»(x, x), 0)] [],
    exact [expr inner_self_nonneg],
    have [ident H₂] [":", expr «expr = »(re «expr⟪ , ⟫»(x, x), 0)] [],
    exact [expr le_antisymm h H₁],
    rw [expr is_R_or_C.ext_iff] [],
    exact [expr ⟨by simp [] [] [] ["[", expr H₂, "]"] [] [], by simp [] [] [] ["[", expr inner_self_nonneg_im, "]"] [] []⟩] },
  { rintro [ident rfl],
    simp [] [] ["only"] ["[", expr inner_zero_left, ",", expr add_monoid_hom.map_zero, "]"] [] [] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem real_inner_self_nonpos {x : F} : «expr ↔ »(«expr ≤ »(«expr⟪ , ⟫_ℝ»(x, x), 0), «expr = »(x, 0)) :=
by { have [ident h] [] [":=", expr @inner_self_nonpos exprℝ() F _ _ x],
  simpa [] [] [] [] [] ["using", expr h] }

@[simp]
theorem inner_self_re_to_K {x : E} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  by 
    rw [IsROrC.ext_iff] <;>
      exact
        ⟨by 
            simp ,
          by 
            simp [inner_self_nonneg_im]⟩

theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (∥x∥^2 : 𝕜) :=
  by 
    suffices  : (IsROrC.re ⟪x, x⟫ : 𝕜) = (∥x∥^2)
    ·
      simpa [inner_self_re_to_K] using this 
    exactModCast (norm_sq_eq_inner x).symm

theorem inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ :=
  by 
    convRHS => rw [←inner_self_re_to_K]
    symm 
    exact IsROrC.abs_of_nonneg inner_self_nonneg

theorem inner_self_abs_to_K {x : E} : (absK ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  by 
    rw [←inner_self_re_abs]
    exact inner_self_re_to_K

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem real_inner_self_abs {x : F} : «expr = »(exprabsR() «expr⟪ , ⟫_ℝ»(x, x), «expr⟪ , ⟫_ℝ»(x, x)) :=
by { have [ident h] [] [":=", expr @inner_self_abs_to_K exprℝ() F _ _ x],
  simpa [] [] [] [] [] ["using", expr h] }

theorem inner_abs_conj_sym {x y : E} : abs ⟪x, y⟫ = abs ⟪y, x⟫ :=
  by 
    rw [←inner_conj_sym, abs_conj]

@[simp]
theorem inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ :=
  by 
    rw [←neg_one_smul 𝕜 x, inner_smul_left]
    simp 

@[simp]
theorem inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ :=
  by 
    rw [←inner_conj_sym, inner_neg_left] <;> simp only [RingEquiv.map_neg, inner_conj_sym]

theorem inner_neg_neg {x y : E} : ⟪-x, -y⟫ = ⟪x, y⟫ :=
  by 
    simp 

@[simp]
theorem inner_self_conj {x : E} : ⟪x, x⟫† = ⟪x, x⟫ :=
  by 
    rw [IsROrC.ext_iff] <;>
      exact
        ⟨by 
            rw [conj_re],
          by 
            rw [conj_im, inner_self_im_zero, neg_zero]⟩

theorem inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ :=
  by 
    simp [sub_eq_add_neg, inner_add_left]

theorem inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ :=
  by 
    simp [sub_eq_add_neg, inner_add_right]

theorem inner_mul_conj_re_abs {x y : E} : re (⟪x, y⟫*⟪y, x⟫) = abs (⟪x, y⟫*⟪y, x⟫) :=
  by 
    rw [←inner_conj_sym, mul_commₓ]
    exact re_eq_abs_of_mul_conj (inner y x)

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self {x y : E} : ⟪x+y, x+y⟫ = ((⟪x, x⟫+⟪x, y⟫)+⟪y, x⟫)+⟪y, y⟫ :=
  by 
    simp only [inner_add_left, inner_add_right] <;> ring

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self
{x
 y : F} : «expr = »(«expr⟪ , ⟫_ℝ»(«expr + »(x, y), «expr + »(x, y)), «expr + »(«expr + »(«expr⟪ , ⟫_ℝ»(x, x), «expr * »(2, «expr⟪ , ⟫_ℝ»(x, y))), «expr⟪ , ⟫_ℝ»(y, y))) :=
begin
  have [] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(y, x), «expr⟪ , ⟫_ℝ»(x, y))] [":=", expr by rw ["[", "<-", expr inner_conj_sym, "]"] []; refl],
  simp [] [] [] ["[", expr inner_add_add_self, ",", expr this, "]"] [] [],
  ring []
end

theorem inner_sub_sub_self {x y : E} : ⟪x - y, x - y⟫ = (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫)+⟪y, y⟫ :=
  by 
    simp only [inner_sub_left, inner_sub_right] <;> ring

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self
{x
 y : F} : «expr = »(«expr⟪ , ⟫_ℝ»(«expr - »(x, y), «expr - »(x, y)), «expr + »(«expr - »(«expr⟪ , ⟫_ℝ»(x, x), «expr * »(2, «expr⟪ , ⟫_ℝ»(x, y))), «expr⟪ , ⟫_ℝ»(y, y))) :=
begin
  have [] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(y, x), «expr⟪ , ⟫_ℝ»(x, y))] [":=", expr by rw ["[", "<-", expr inner_conj_sym, "]"] []; refl],
  simp [] [] [] ["[", expr inner_sub_sub_self, ",", expr this, "]"] [] [],
  ring []
end

/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : (⟪x+y, x+y⟫+⟪x - y, x - y⟫) = 2*⟪x, x⟫+⟪y, y⟫ :=
  by 
    simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_commₓ, add_left_commₓ]

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
theorem inner_mul_inner_self_le
(x
 y : E) : «expr ≤ »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), «expr * »(re «expr⟪ , ⟫»(x, x), re «expr⟪ , ⟫»(y, y))) :=
begin
  by_cases [expr hy, ":", expr «expr = »(y, 0)],
  { rw ["[", expr hy, "]"] [],
    simp [] [] ["only"] ["[", expr is_R_or_C.abs_zero, ",", expr inner_zero_left, ",", expr mul_zero, ",", expr add_monoid_hom.map_zero, "]"] [] [] },
  { change [expr «expr ≠ »(y, 0)] [] ["at", ident hy],
    have [ident hy'] [":", expr «expr ≠ »(«expr⟪ , ⟫»(y, y), 0)] [":=", expr λ
     h, by rw ["[", expr inner_self_eq_zero, "]"] ["at", ident h]; exact [expr hy h]],
    set [] [ident T] [] [":="] [expr «expr / »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(y, y))] ["with", ident hT],
    have [ident h₁] [":", expr «expr = »(re «expr⟪ , ⟫»(y, x), re «expr⟪ , ⟫»(x, y))] [":=", expr inner_re_symm],
    have [ident h₂] [":", expr «expr = »(im «expr⟪ , ⟫»(y, x), «expr- »(im «expr⟪ , ⟫»(x, y)))] [":=", expr inner_im_symm],
    have [ident h₃] [":", expr «expr = »(«expr / »(«expr * »(«expr * »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(x, y)), «expr⟪ , ⟫»(y, y)), «expr * »(«expr⟪ , ⟫»(y, y), «expr⟪ , ⟫»(y, y))), «expr / »(«expr * »(«expr⟪ , ⟫»(y, x), «expr⟪ , ⟫»(x, y)), «expr⟪ , ⟫»(y, y)))] [],
    { rw ["[", expr mul_div_assoc, "]"] [],
      have [] [":", expr «expr = »(«expr / »(«expr⟪ , ⟫»(y, y), «expr * »(«expr⟪ , ⟫»(y, y), «expr⟪ , ⟫»(y, y))), «expr / »(1, «expr⟪ , ⟫»(y, y)))] [":=", expr by rw ["[", expr div_mul_eq_div_mul_one_div, ",", expr div_self hy', ",", expr one_mul, "]"] []],
      rw ["[", expr this, ",", expr div_eq_mul_inv, ",", expr one_mul, ",", "<-", expr div_eq_mul_inv, "]"] [] },
    have [ident h₄] [":", expr «expr = »(«expr⟪ , ⟫»(y, y), re «expr⟪ , ⟫»(y, y))] [":=", expr by simp [] [] [] [] [] []],
    have [ident h₅] [":", expr «expr > »(re «expr⟪ , ⟫»(y, y), 0)] [],
    { refine [expr lt_of_le_of_ne inner_self_nonneg _],
      intro [ident H],
      apply [expr hy'],
      rw [expr is_R_or_C.ext_iff] [],
      exact [expr ⟨by simp [] [] ["only"] ["[", expr H, ",", expr zero_re', "]"] [] [], by simp [] [] ["only"] ["[", expr inner_self_nonneg_im, ",", expr add_monoid_hom.map_zero, "]"] [] []⟩] },
    have [ident h₆] [":", expr «expr ≠ »(re «expr⟪ , ⟫»(y, y), 0)] [":=", expr ne_of_gt h₅],
    have [ident hmain] [] [":=", expr calc
       «expr ≤ »(0, re «expr⟪ , ⟫»(«expr - »(x, «expr • »(T, y)), «expr - »(x, «expr • »(T, y)))) : inner_self_nonneg
       «expr = »(..., «expr + »(«expr - »(«expr - »(re «expr⟪ , ⟫»(x, x), re «expr⟪ , ⟫»(«expr • »(T, y), x)), re «expr⟪ , ⟫»(x, «expr • »(T, y))), re «expr⟪ , ⟫»(«expr • »(T, y), «expr • »(T, y)))) : by simp [] [] ["only"] ["[", expr inner_sub_sub_self, ",", expr inner_smul_left, ",", expr inner_smul_right, ",", expr h₁, ",", expr h₂, ",", expr neg_mul_eq_neg_mul_symm, ",", expr add_monoid_hom.map_add, ",", expr conj_im, ",", expr add_monoid_hom.map_sub, ",", expr mul_neg_eq_neg_mul_symm, ",", expr conj_re, ",", expr neg_neg, ",", expr mul_re, "]"] [] []
       «expr = »(..., «expr + »(«expr - »(«expr - »(re «expr⟪ , ⟫»(x, x), re «expr * »(«expr †»(T), «expr⟪ , ⟫»(y, x))), re «expr * »(T, «expr⟪ , ⟫»(x, y))), re «expr * »(«expr * »(T, «expr †»(T)), «expr⟪ , ⟫»(y, y)))) : by simp [] [] ["only"] ["[", expr inner_smul_left, ",", expr inner_smul_right, ",", expr mul_assoc, "]"] [] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr * »(«expr / »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, y)), «expr⟪ , ⟫»(y, x)))) : by field_simp [] ["[", "-", ident mul_re, ",", expr hT, ",", expr ring_equiv.map_div, ",", expr h₁, ",", expr h₃, ",", expr inner_conj_sym, "]"] [] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr / »(«expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr div_mul_eq_mul_div_comm, ",", "<-", expr mul_div_assoc, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), re «expr / »(«expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by conv_lhs [] [] { rw ["[", expr h₄, "]"] }
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(re «expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr div_re_of_real, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(abs «expr * »(«expr⟪ , ⟫»(x, y), «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw ["[", expr inner_mul_conj_re_abs, "]"] []
       «expr = »(..., «expr - »(re «expr⟪ , ⟫»(x, x), «expr / »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)))) : by rw [expr is_R_or_C.abs_mul] []],
    have [ident hmain'] [":", expr «expr ≤ »(«expr / »(«expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)), re «expr⟪ , ⟫»(y, y)), re «expr⟪ , ⟫»(x, x))] [":=", expr by linarith [] [] []],
    have [] [] [":=", expr (mul_le_mul_right h₅).mpr hmain'],
    rwa ["[", expr div_mul_cancel «expr * »(abs «expr⟪ , ⟫»(x, y), abs «expr⟪ , ⟫»(y, x)) h₆, "]"] ["at", ident this] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le
(x
 y : F) : «expr ≤ »(«expr * »(«expr⟪ , ⟫_ℝ»(x, y), «expr⟪ , ⟫_ℝ»(x, y)), «expr * »(«expr⟪ , ⟫_ℝ»(x, x), «expr⟪ , ⟫_ℝ»(y, y))) :=
begin
  have [ident h₁] [":", expr «expr = »(«expr⟪ , ⟫_ℝ»(y, x), «expr⟪ , ⟫_ℝ»(x, y))] [":=", expr by rw ["[", "<-", expr inner_conj_sym, "]"] []; refl],
  have [ident h₂] [] [":=", expr @inner_mul_inner_self_le exprℝ() F _ _ x y],
  dsimp [] [] [] ["at", ident h₂],
  have [ident h₃] [] [":=", expr abs_mul_abs_self «expr⟪ , ⟫_ℝ»(x, y)],
  rw ["[", expr h₁, "]"] ["at", ident h₂],
  simpa [] [] [] ["[", expr h₃, "]"] [] ["using", expr h₂]
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linear_independent_of_ne_zero_of_inner_eq_zero
{ι : Type*}
{v : ι → E}
(hz : ∀ i, «expr ≠ »(v i, 0))
(ho : ∀ i j, «expr ≠ »(i, j) → «expr = »(«expr⟪ , ⟫»(v i, v j), 0)) : linear_independent 𝕜 v :=
begin
  rw [expr linear_independent_iff'] [],
  intros [ident s, ident g, ident hg, ident i, ident hi],
  have [ident h'] [":", expr «expr = »(«expr * »(g i, inner (v i) (v i)), inner (v i) «expr∑ in , »((j), s, «expr • »(g j, v j)))] [],
  { rw [expr inner_sum] [],
    symmetry,
    convert [] [expr finset.sum_eq_single i _ _] [],
    { rw [expr inner_smul_right] [] },
    { intros [ident j, ident hj, ident hji],
      rw ["[", expr inner_smul_right, ",", expr ho i j hji.symm, ",", expr mul_zero, "]"] [] },
    { exact [expr λ h, false.elim (h hi)] } },
  simpa [] [] [] ["[", expr hg, ",", expr hz, "]"] [] ["using", expr h']
end

end BasicProperties

section OrthonormalSets

variable {ι : Type _} (𝕜)

include 𝕜

/-- An orthonormal set of vectors in an `inner_product_space` -/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ∥v i∥ = 1) ∧ ∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0

omit 𝕜

variable {𝕜}

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
theorem orthonormal_iff_ite
{v : ι → E} : «expr ↔ »(orthonormal 𝕜 v, ∀
 i j, «expr = »(«expr⟪ , ⟫»(v i, v j), if «expr = »(i, j) then (1 : 𝕜) else (0 : 𝕜))) :=
begin
  split,
  { intros [ident hv, ident i, ident j],
    split_ifs [] [],
    { simp [] [] [] ["[", expr h, ",", expr inner_self_eq_norm_sq_to_K, ",", expr hv.1, "]"] [] [] },
    { exact [expr hv.2 h] } },
  { intros [ident h],
    split,
    { intros [ident i],
      have [ident h'] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(v i), 2), «expr ^ »(1, 2))] [":=", expr by simp [] [] [] ["[", expr norm_sq_eq_inner, ",", expr h i i, "]"] [] []],
      have [ident h₁] [":", expr «expr ≤ »(0, «expr∥ ∥»(v i))] [":=", expr norm_nonneg _],
      have [ident h₂] [":", expr «expr ≤ »((0 : exprℝ()), 1)] [":=", expr zero_le_one],
      rwa [expr sq_eq_sq h₁ h₂] ["at", ident h'] },
    { intros [ident i, ident j, ident hij],
      simpa [] [] [] ["[", expr hij, "]"] [] ["using", expr h i j] } }
end

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {s : Set E} :
  Orthonormal 𝕜 (coeₓ : s → E) ↔ ∀ v _ : v ∈ s, ∀ w _ : w ∈ s, ⟪v, w⟫ = if v = w then 1 else 0 :=
  by 
    rw [orthonormal_iff_ite]
    split 
    ·
      intro h v hv w hw 
      convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1
      simp 
    ·
      rintro h ⟨v, hv⟩ ⟨w, hw⟩
      convert h v hv w hw using 1
      simp 

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = l i :=
  by 
    simp [Finsupp.total_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪v i, ∑i : ι, l i • v i⟫ = l i :=
  by 
    simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
  ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) :=
  by 
    rw [←inner_conj_sym, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
  ⟪∑i : ι, l i • v i, v i⟫ = conj (l i) :=
  by 
    simp [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv]

/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal 𝕜 v) {a : ι → ι → 𝕜} :
  (∑i in s, ∑j in s, a i j • ⟪v j, v i⟫) = ∑k in s, a k k :=
  by 
    simp [orthonormal_iff_ite.mp hv, Finset.sum_ite_of_true]

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An orthonormal set is linearly independent. -/
theorem orthonormal.linear_independent {v : ι → E} (hv : orthonormal 𝕜 v) : linear_independent 𝕜 v :=
begin
  rw [expr linear_independent_iff] [],
  intros [ident l, ident hl],
  ext [] [ident i] [],
  have [ident key] [":", expr «expr = »(«expr⟪ , ⟫»(v i, finsupp.total ι E 𝕜 v l), «expr⟪ , ⟫»(v i, 0))] [":=", expr by rw [expr hl] []],
  simpa [] [] [] ["[", expr hv.inner_right_finsupp, "]"] [] ["using", expr key]
end

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
theorem Orthonormal.comp {ι' : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) (f : ι' → ι) (hf : Function.Injective f) :
  Orthonormal 𝕜 (v ∘ f) :=
  by 
    rw [orthonormal_iff_ite] at hv⊢
    intro i j 
    convert hv (f i) (f j) using 1
    simp [hf.eq_iff]

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι} (hi : i ∉ s)
  {l : ι →₀ 𝕜} (hl : l ∈ Finsupp.supported 𝕜 𝕜 s) : ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = 0 :=
  by 
    rw [Finsupp.mem_supported'] at hl 
    simp [hv.inner_left_finsupp, hl i hi]

variable (𝕜 E)

theorem orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) → E) :=
  by 
    simp [orthonormal_subtype_iff_ite]

variable {𝕜 E}

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orthonormal_Union_of_directed
{η : Type*}
{s : η → set E}
(hs : directed ((«expr ⊆ »)) s)
(h : ∀ i, orthonormal 𝕜 (λ x, x : s i → E)) : orthonormal 𝕜 (λ x, x : «expr⋃ , »((i), s i) → E) :=
begin
  rw [expr orthonormal_subtype_iff_ite] [],
  rintros [ident x, "⟨", "_", ",", "⟨", ident i, ",", ident rfl, "⟩", ",", ident hxi, "⟩", ident y, "⟨", "_", ",", "⟨", ident j, ",", ident rfl, "⟩", ",", ident hyj, "⟩"],
  obtain ["⟨", ident k, ",", ident hik, ",", ident hjk, "⟩", ":=", expr hs i j],
  have [ident h_orth] [":", expr orthonormal 𝕜 (λ x, x : s k → E)] [":=", expr h k],
  rw [expr orthonormal_subtype_iff_ite] ["at", ident h_orth],
  exact [expr h_orth x (hik hxi) y (hjk hyj)]
end

theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
  (h : ∀ a _ : a ∈ s, Orthonormal 𝕜 (fun x => x : (a : Set E) → E)) : Orthonormal 𝕜 (fun x => x : ⋃₀s → E) :=
  by 
    rw [Set.sUnion_eq_Union] <;>
      exact
        orthonormal_Union_of_directed hs.directed_coe
          (by 
            simpa using h)

/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (coeₓ : s → E)) :
  ∃ (w : _)(_ : w ⊇ s), Orthonormal 𝕜 (coeₓ : w → E) ∧ ∀ u _ : u ⊇ w, Orthonormal 𝕜 (coeₓ : u → E) → u = w :=
  by 
    rcases Zorn.zorn_subset_nonempty { b | Orthonormal 𝕜 (coeₓ : b → E) } _ _ hs with ⟨b, bi, sb, h⟩
    ·
      refine' ⟨b, sb, bi, _⟩
      exact fun u hus hu => h u hu hus
    ·
      refine' fun c hc cc c0 => ⟨⋃₀c, _, _⟩
      ·
        exact orthonormal_sUnion_of_directed cc.directed_on fun x xc => hc xc
      ·
        exact fun _ => Set.subset_sUnion_of_mem

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orthonormal.ne_zero {v : ι → E} (hv : orthonormal 𝕜 v) (i : ι) : «expr ≠ »(v i, 0) :=
begin
  have [] [":", expr «expr ≠ »(«expr∥ ∥»(v i), 0)] [],
  { rw [expr hv.1 i] [],
    norm_num [] [] },
  simpa [] [] [] [] [] ["using", expr this]
end

open FiniteDimensional

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
  (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.linear_independent card_eq

@[simp]
theorem coe_basis_of_orthonormal_of_card_eq_finrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
  (card_eq : Fintype.card ι = finrank 𝕜 E) : (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basis_of_linear_independent_of_card_eq_finrank _ _

end OrthonormalSets

section Norm

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq_sqrt_inner (x : E) : «expr = »(«expr∥ ∥»(x), sqrt (re «expr⟪ , ⟫»(x, x))) :=
begin
  have [ident h₁] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(x), 2), re «expr⟪ , ⟫»(x, x))] [":=", expr norm_sq_eq_inner x],
  have [ident h₂] [] [":=", expr congr_arg sqrt h₁],
  simpa [] [] [] [] [] ["using", expr h₂]
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem norm_eq_sqrt_real_inner (x : F) : «expr = »(«expr∥ ∥»(x), sqrt «expr⟪ , ⟫_ℝ»(x, x)) :=
by { have [ident h] [] [":=", expr @norm_eq_sqrt_inner exprℝ() F _ _ x],
  simpa [] [] [] [] [] ["using", expr h] }

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ∥x∥*∥x∥ :=
  by 
    rw [norm_eq_sqrt_inner, ←sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = (∥x∥^2) :=
  by 
    rw [pow_two, inner_self_eq_norm_mul_norm]

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem real_inner_self_eq_norm_mul_norm
(x : F) : «expr = »(«expr⟪ , ⟫_ℝ»(x, x), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x))) :=
by { have [ident h] [] [":=", expr @inner_self_eq_norm_mul_norm exprℝ() F _ _ x],
  simpa [] [] [] [] [] ["using", expr h] }

theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = (∥x∥^2) :=
  by 
    rw [pow_two, real_inner_self_eq_norm_mul_norm]

/-- Expand the square -/
theorem norm_add_sq {x y : E} : (∥x+y∥^2) = ((∥x∥^2)+2*re ⟪x, y⟫)+∥y∥^2 :=
  by 
    repeat' 
      rw [sq, ←inner_self_eq_norm_mul_norm]
    rw [inner_add_add_self, two_mul]
    simp only [add_assocₓ, add_left_injₓ, add_right_injₓ, AddMonoidHom.map_add]
    rw [←inner_conj_sym, conj_re]

alias norm_add_sq ← norm_add_pow_two

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expand the square -/
theorem norm_add_sq_real
{x
 y : F} : «expr = »(«expr ^ »(«expr∥ ∥»(«expr + »(x, y)), 2), «expr + »(«expr + »(«expr ^ »(«expr∥ ∥»(x), 2), «expr * »(2, «expr⟪ , ⟫_ℝ»(x, y))), «expr ^ »(«expr∥ ∥»(y), 2))) :=
by { have [ident h] [] [":=", expr @norm_add_sq exprℝ() F _ _],
  simpa [] [] [] [] [] ["using", expr h] }

alias norm_add_sq_real ← norm_add_pow_two_real

/-- Expand the square -/
theorem norm_add_mul_self {x y : E} : (∥x+y∥*∥x+y∥) = ((∥x∥*∥x∥)+2*re ⟪x, y⟫)+∥y∥*∥y∥ :=
  by 
    repeat' 
      rw [←sq]
    exact norm_add_sq

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expand the square -/
theorem norm_add_mul_self_real
{x
 y : F} : «expr = »(«expr * »(«expr∥ ∥»(«expr + »(x, y)), «expr∥ ∥»(«expr + »(x, y))), «expr + »(«expr + »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x)), «expr * »(2, «expr⟪ , ⟫_ℝ»(x, y))), «expr * »(«expr∥ ∥»(y), «expr∥ ∥»(y)))) :=
by { have [ident h] [] [":=", expr @norm_add_mul_self exprℝ() F _ _],
  simpa [] [] [] [] [] ["using", expr h] }

/-- Expand the square -/
theorem norm_sub_sq {x y : E} : (∥x - y∥^2) = ((∥x∥^2) - 2*re ⟪x, y⟫)+∥y∥^2 :=
  by 
    repeat' 
      rw [sq, ←inner_self_eq_norm_mul_norm]
    rw [inner_sub_sub_self]
    calc re ((⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫)+⟪y, y⟫) = (re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫)+re ⟪y, y⟫ :=
      by 
        simp _ = ((-re ⟪y, x⟫ - re ⟪x, y⟫)+re ⟪x, x⟫)+re ⟪y, y⟫ :=
      by 
        ring _ = ((-re (⟪x, y⟫†) - re ⟪x, y⟫)+re ⟪x, x⟫)+re ⟪y, y⟫ :=
      by 
        rw [inner_conj_sym]_ = ((-re ⟪x, y⟫ - re ⟪x, y⟫)+re ⟪x, x⟫)+re ⟪y, y⟫ :=
      by 
        rw [conj_re]_ = (re ⟪x, x⟫ - 2*re ⟪x, y⟫)+re ⟪y, y⟫ :=
      by 
        ring

alias norm_sub_sq ← norm_sub_pow_two

/-- Expand the square -/
theorem norm_sub_sq_real {x y : F} : (∥x - y∥^2) = ((∥x∥^2) - 2*⟪x, y⟫_ℝ)+∥y∥^2 :=
  norm_sub_sq

alias norm_sub_sq_real ← norm_sub_pow_two_real

/-- Expand the square -/
theorem norm_sub_mul_self {x y : E} : (∥x - y∥*∥x - y∥) = ((∥x∥*∥x∥) - 2*re ⟪x, y⟫)+∥y∥*∥y∥ :=
  by 
    repeat' 
      rw [←sq]
    exact norm_sub_sq

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Expand the square -/
theorem norm_sub_mul_self_real
{x
 y : F} : «expr = »(«expr * »(«expr∥ ∥»(«expr - »(x, y)), «expr∥ ∥»(«expr - »(x, y))), «expr + »(«expr - »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x)), «expr * »(2, «expr⟪ , ⟫_ℝ»(x, y))), «expr * »(«expr∥ ∥»(y), «expr∥ ∥»(y)))) :=
by { have [ident h] [] [":=", expr @norm_sub_mul_self exprℝ() F _ _],
  simpa [] [] [] [] [] ["using", expr h] }

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : E) : «expr ≤ »(abs «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))) :=
nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (begin
   have [] [":", expr «expr = »(«expr * »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), «expr * »(re «expr⟪ , ⟫»(x, x), re «expr⟪ , ⟫»(y, y)))] [],
   simp [] [] ["only"] ["[", expr inner_self_eq_norm_mul_norm, "]"] [] [],
   ring [],
   rw [expr this] [],
   conv_lhs [] [] { congr,
     skip,
     rw ["[", expr inner_abs_conj_sym, "]"] },
   exact [expr inner_mul_inner_self_le _ _]
 end)

theorem norm_inner_le_norm (x y : E) : ∥⟪x, y⟫∥ ≤ ∥x∥*∥y∥ :=
  (IsROrC.norm_eq_abs _).le.trans (abs_inner_le_norm x y)

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm
(x y : F) : «expr ≤ »(exprabsR() «expr⟪ , ⟫_ℝ»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))) :=
by { have [ident h] [] [":=", expr @abs_inner_le_norm exprℝ() F _ _ x y],
  simpa [] [] [] [] [] ["using", expr h] }

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ∥x∥*∥y∥ :=
  le_transₓ (le_abs_self _) (abs_real_inner_le_norm _ _)

include 𝕜

theorem parallelogram_law_with_norm {x y : E} : ((∥x+y∥*∥x+y∥)+∥x - y∥*∥x - y∥) = 2*(∥x∥*∥x∥)+∥y∥*∥y∥ :=
  by 
    simp only [←inner_self_eq_norm_mul_norm]
    rw [←re.map_add, parallelogram_law, two_mul, two_mul]
    simp only [re.map_add]

omit 𝕜

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem parallelogram_law_with_norm_real
{x
 y : F} : «expr = »(«expr + »(«expr * »(«expr∥ ∥»(«expr + »(x, y)), «expr∥ ∥»(«expr + »(x, y))), «expr * »(«expr∥ ∥»(«expr - »(x, y)), «expr∥ ∥»(«expr - »(x, y)))), «expr * »(2, «expr + »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x)), «expr * »(«expr∥ ∥»(y), «expr∥ ∥»(y))))) :=
by { have [ident h] [] [":=", expr @parallelogram_law_with_norm exprℝ() F _ _ x y],
  simpa [] [] [] [] [] ["using", expr h] }

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (((∥x+y∥*∥x+y∥) - ∥x∥*∥x∥) - ∥y∥*∥y∥) / 2 :=
  by 
    rw [norm_add_mul_self]
    ring

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
  re ⟪x, y⟫ = (((∥x∥*∥x∥)+∥y∥*∥y∥) - ∥x - y∥*∥x - y∥) / 2 :=
  by 
    rw [norm_sub_mul_self]
    ring

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
  re ⟪x, y⟫ = ((∥x+y∥*∥x+y∥) - ∥x - y∥*∥x - y∥) / 4 :=
  by 
    rw [norm_add_mul_self, norm_sub_mul_self]
    ring

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four (x y : E) :
  im ⟪x, y⟫ = ((∥x - IK • y∥*∥x - IK • y∥) - ∥x+IK • y∥*∥x+IK • y∥) / 4 :=
  by 
    simp only [norm_add_mul_self, norm_sub_mul_self, inner_smul_right, I_mul_re]
    ring

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
  ⟪x, y⟫ = (((∥x+y∥^2) - (∥x - y∥^2))+((∥x - IK • y∥^2) - (∥x+IK • y∥^2))*IK) / 4 :=
  by 
    rw [←re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
      im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four]
    pushCast 
    simp only [sq, ←mul_div_right_comm, ←add_div]

section 

variable {E' : Type _} [InnerProductSpace 𝕜 E']

/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  by 
    simp [inner_eq_sum_norm_sq_div_four, ←f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.to_linear_isometry.inner_map_map x y

/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f,
    fun x =>
      by 
        simp only [norm_eq_sqrt_inner, h]⟩

@[simp]
theorem LinearMap.coe_isometry_of_inner (f : E →ₗ[𝕜] E') h : «expr⇑ » (f.isometry_of_inner h) = f :=
  rfl

@[simp]
theorem LinearMap.isometry_of_inner_to_linear_map (f : E →ₗ[𝕜] E') h : (f.isometry_of_inner h).toLinearMap = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]
theorem LinearEquiv.coe_isometry_of_inner (f : E ≃ₗ[𝕜] E') h : «expr⇑ » (f.isometry_of_inner h) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometry_of_inner_to_linear_equiv (f : E ≃ₗ[𝕜] E') h : (f.isometry_of_inner h).toLinearEquiv = f :=
  rfl

end 

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (((∥x+y∥*∥x+y∥) - ∥x∥*∥x∥) - ∥y∥*∥y∥) / 2 :=
  re_to_real.symm.trans$ re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
  ⟪x, y⟫_ℝ = (((∥x∥*∥x∥)+∥y∥*∥y∥) - ∥x - y∥*∥x - y∥) / 2 :=
  re_to_real.symm.trans$ re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
  ((∥x+y∥*∥x+y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥) ↔ ⟪x, y⟫_ℝ = 0 :=
  by 
    rw [norm_add_mul_self, add_right_cancel_iffₓ, add_right_eq_selfₓ, mul_eq_zero]
    normNum

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
  (∥x+y∥*∥x+y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥ :=
  by 
    rw [norm_add_mul_self, add_right_cancel_iffₓ, add_right_eq_selfₓ, mul_eq_zero]
    apply Or.inr 
    simp only [h, zero_re']

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) : (∥x+y∥*∥x+y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
  ((∥x - y∥*∥x - y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥) ↔ ⟪x, y⟫_ℝ = 0 :=
  by 
    rw [norm_sub_mul_self, add_right_cancel_iffₓ, sub_eq_add_neg, add_right_eq_selfₓ, neg_eq_zero, mul_eq_zero]
    normNum

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) : (∥x - y∥*∥x - y∥) = (∥x∥*∥x∥)+∥y∥*∥y∥ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x+y, x - y⟫_ℝ = 0 ↔ ∥x∥ = ∥y∥ :=
  by 
    convRHS => rw [←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
    simp only [←inner_self_eq_norm_mul_norm, inner_add_left, inner_sub_right, real_inner_comm y x, sub_eq_zero,
      re_to_real]
    split 
    ·
      intro h 
      rw [add_commₓ] at h 
      linarith
    ·
      intro h 
      linarith

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ∥w - v∥ = ∥w+v∥ :=
  by 
    rw [←mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
    simp [h, ←inner_self_eq_norm_mul_norm, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
      inner_re_symm]

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : absR (⟪x, y⟫_ℝ / ∥x∥*∥y∥) ≤ 1 :=
  by 
    rw [_root_.abs_div]
    byCases' h : 0 = absR (∥x∥*∥y∥)
    ·
      rw [←h, div_zero]
      normNum
    ·
      change 0 ≠ absR (∥x∥*∥y∥) at h 
      rw [div_le_iff' (lt_of_le_of_neₓ (ge_iff_le.mp (_root_.abs_nonneg (∥x∥*∥y∥))) h)]
      convert abs_real_inner_le_norm x y using 1
      rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y), mul_oneₓ]

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r*∥x∥*∥x∥ :=
  by 
    rw [real_inner_smul_left, ←real_inner_self_eq_norm_mul_norm]

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r*∥x∥*∥x∥ :=
  by 
    rw [inner_smul_right, ←real_inner_self_eq_norm_mul_norm]

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul
{x : E}
{r : 𝕜}
(hx : «expr ≠ »(x, 0))
(hr : «expr ≠ »(r, 0)) : «expr = »(«expr / »(abs «expr⟪ , ⟫»(x, «expr • »(r, x)), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(«expr • »(r, x)))), 1) :=
begin
  have [ident hx'] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr norm_eq_zero, ",", expr hx, "]"] [] []],
  have [ident hr'] [":", expr «expr ≠ »(abs r, 0)] [":=", expr by simp [] [] [] ["[", expr is_R_or_C.abs_eq_zero, ",", expr hr, "]"] [] []],
  rw ["[", expr inner_smul_right, ",", expr is_R_or_C.abs_mul, ",", "<-", expr inner_self_re_abs, ",", expr inner_self_eq_norm_mul_norm, ",", expr norm_smul, "]"] [],
  rw ["[", expr is_R_or_C.norm_eq_abs, ",", "<-", expr mul_assoc, ",", "<-", expr div_div_eq_div_mul, ",", expr mul_div_cancel _ hx', ",", "<-", expr div_div_eq_div_mul, ",", expr mul_comm, ",", expr mul_div_cancel _ hr', ",", expr div_self hx', "]"] []
end

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) :
  (absR ⟪x, r • x⟫_ℝ / ∥x∥*∥r • x∥) = 1 :=
  by 
    rw [←abs_to_real]
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) :
  (⟪x, r • x⟫_ℝ / ∥x∥*∥r • x∥) = 1 :=
  by 
    rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ←mul_assocₓ ∥x∥, mul_commₓ _ (absR r), mul_assocₓ,
      _root_.abs_of_nonneg (le_of_ltₓ hr), div_self]
    exact mul_ne_zero (ne_of_gtₓ hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) :
  (⟪x, r • x⟫_ℝ / ∥x∥*∥r • x∥) = -1 :=
  by 
    rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ←mul_assocₓ ∥x∥, mul_commₓ _ (absR r), mul_assocₓ,
      abs_of_neg hr, ←neg_mul_eq_neg_mul, div_neg_eq_neg_div, div_self]
    exact mul_ne_zero (ne_of_ltₓ hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_inner_div_norm_mul_norm_eq_one_iff
(x
 y : E) : «expr ↔ »(«expr = »(abs «expr / »(«expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), 1), «expr ∧ »(«expr ≠ »(x, 0), «expr∃ , »((r : 𝕜), «expr ∧ »(«expr ≠ »(r, 0), «expr = »(y, «expr • »(r, x)))))) :=
begin
  split,
  { intro [ident h],
    have [ident hx0] [":", expr «expr ≠ »(x, 0)] [],
    { intro [ident hx0],
      rw ["[", expr hx0, ",", expr inner_zero_left, ",", expr zero_div, "]"] ["at", ident h],
      norm_num [] ["at", ident h] },
    refine [expr and.intro hx0 _],
    set [] [ident r] [] [":="] [expr «expr / »(«expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(x)))] ["with", ident hr],
    use [expr r],
    set [] [ident t] [] [":="] [expr «expr - »(y, «expr • »(r, x))] ["with", ident ht],
    have [ident ht0] [":", expr «expr = »(«expr⟪ , ⟫»(x, t), 0)] [],
    { rw ["[", expr ht, ",", expr inner_sub_right, ",", expr inner_smul_right, ",", expr hr, "]"] [],
      norm_cast [],
      rw ["[", "<-", expr inner_self_eq_norm_mul_norm, ",", expr inner_self_re_to_K, ",", expr div_mul_cancel _ (λ
        h, hx0 (inner_self_eq_zero.1 h)), ",", expr sub_self, "]"] [] },
    replace [ident h] [":", expr «expr = »(«expr / »(«expr∥ ∥»(«expr • »(r, x)), «expr∥ ∥»(«expr + »(t, «expr • »(r, x)))), 1)] [],
    { rw ["[", "<-", expr sub_add_cancel y «expr • »(r, x), ",", "<-", expr ht, ",", expr inner_add_right, ",", expr ht0, ",", expr zero_add, ",", expr inner_smul_right, ",", expr is_R_or_C.abs_div, ",", expr is_R_or_C.abs_mul, ",", "<-", expr inner_self_re_abs, ",", expr inner_self_eq_norm_mul_norm, "]"] ["at", ident h],
      norm_cast ["at", ident h],
      rwa ["[", expr _root_.abs_mul, ",", expr abs_norm_eq_norm, ",", expr abs_norm_eq_norm, ",", "<-", expr mul_assoc, ",", expr mul_comm, ",", expr mul_div_mul_left _ _ (λ
        h, hx0 (norm_eq_zero.1 h)), ",", "<-", expr is_R_or_C.norm_eq_abs, ",", "<-", expr norm_smul, "]"] ["at", ident h] },
    have [ident hr0] [":", expr «expr ≠ »(r, 0)] [],
    { intro [ident hr0],
      rw ["[", expr hr0, ",", expr zero_smul, ",", expr norm_zero, ",", expr zero_div, "]"] ["at", ident h],
      norm_num [] ["at", ident h] },
    refine [expr and.intro hr0 _],
    have [ident h2] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(«expr • »(r, x)), 2), «expr ^ »(«expr∥ ∥»(«expr + »(t, «expr • »(r, x))), 2))] [],
    { rw ["[", expr eq_of_div_eq_one h, "]"] [] },
    replace [ident h2] [":", expr «expr = »(«expr⟪ , ⟫»(«expr • »(r, x), «expr • »(r, x)), «expr + »(«expr + »(«expr + »(«expr⟪ , ⟫»(t, t), «expr⟪ , ⟫»(t, «expr • »(r, x))), «expr⟪ , ⟫»(«expr • »(r, x), t)), «expr⟪ , ⟫»(«expr • »(r, x), «expr • »(r, x))))] [],
    { rw ["[", expr sq, ",", expr sq, ",", "<-", expr inner_self_eq_norm_mul_norm, ",", "<-", expr inner_self_eq_norm_mul_norm, "]"] ["at", ident h2],
      have [ident h2'] [] [":=", expr congr_arg (λ z : exprℝ(), (z : 𝕜)) h2],
      simp_rw ["[", expr inner_self_re_to_K, ",", expr inner_add_add_self, "]"] ["at", ident h2'],
      exact [expr h2'] },
    conv ["at", ident h2] ["in", expr «expr⟪ , ⟫»(«expr • »(r, x), t)] { rw ["[", expr inner_smul_left, ",", expr ht0, ",", expr mul_zero, "]"] },
    symmetry' ["at", ident h2],
    have [ident h₁] [":", expr «expr = »(«expr⟪ , ⟫»(t, «expr • »(r, x)), 0)] [":=", expr by { rw ["[", expr inner_smul_right, ",", "<-", expr inner_conj_sym, ",", expr ht0, "]"] [],
       simp [] [] [] [] [] [] }],
    rw ["[", expr add_zero, ",", expr h₁, ",", expr add_left_eq_self, ",", expr add_zero, ",", expr inner_self_eq_zero, "]"] ["at", ident h2],
    rw [expr h2] ["at", ident ht],
    exact [expr eq_of_sub_eq_zero ht.symm] },
  { intro [ident h],
    rcases [expr h, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hy, "⟩", "⟩", "⟩"],
    rw ["[", expr hy, ",", expr is_R_or_C.abs_div, "]"] [],
    norm_cast [],
    rw ["[", expr _root_.abs_mul, ",", expr abs_norm_eq_norm, ",", expr abs_norm_eq_norm, "]"] [],
    exact [expr abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff
(x
 y : F) : «expr ↔ »(«expr = »(exprabsR() «expr / »(«expr⟪ , ⟫_ℝ»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), 1), «expr ∧ »(«expr ≠ »(x, 0), «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr ≠ »(r, 0), «expr = »(y, «expr • »(r, x)))))) :=
begin
  have [] [] [":=", expr @abs_inner_div_norm_mul_norm_eq_one_iff exprℝ() F _ _ x y],
  simpa [] [] [] ["[", expr coe_real_eq_id, "]"] [] ["using", expr this]
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem abs_inner_eq_norm_iff
(x y : E)
(hx0 : «expr ≠ »(x, 0))
(hy0 : «expr ≠ »(y, 0)) : «expr ↔ »(«expr = »(abs «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), «expr∃ , »((r : 𝕜), «expr ∧ »(«expr ≠ »(r, 0), «expr = »(y, «expr • »(r, x))))) :=
begin
  have [ident hx0'] [":", expr «expr ≠ »(«expr∥ ∥»(x), 0)] [":=", expr by simp [] [] [] ["[", expr norm_eq_zero, ",", expr hx0, "]"] [] []],
  have [ident hy0'] [":", expr «expr ≠ »(«expr∥ ∥»(y), 0)] [":=", expr by simp [] [] [] ["[", expr norm_eq_zero, ",", expr hy0, "]"] [] []],
  have [ident hxy0] [":", expr «expr ≠ »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)), 0)] [":=", expr by simp [] [] [] ["[", expr hx0', ",", expr hy0', "]"] [] []],
  have [ident h₁] [":", expr «expr ↔ »(«expr = »(abs «expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), «expr = »(abs «expr / »(«expr⟪ , ⟫»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), 1))] [],
  { refine [expr ⟨_, _⟩],
    { intro [ident h],
      norm_cast [],
      rw ["[", expr is_R_or_C.abs_div, ",", expr h, ",", expr abs_of_real, ",", expr _root_.abs_mul, ",", expr abs_norm_eq_norm, ",", expr abs_norm_eq_norm, "]"] [],
      exact [expr div_self hxy0] },
    { intro [ident h],
      norm_cast ["at", ident h],
      rwa ["[", expr is_R_or_C.abs_div, ",", expr abs_of_real, ",", expr _root_.abs_mul, ",", expr abs_norm_eq_norm, ",", expr abs_norm_eq_norm, ",", expr div_eq_one_iff_eq hxy0, "]"] ["at", ident h] } },
  rw ["[", expr h₁, ",", expr abs_inner_div_norm_mul_norm_eq_one_iff x y, "]"] [],
  have [] [":", expr «expr ≠ »(x, 0)] [":=", expr λ h, «expr $ »(hx0', norm_eq_zero.mpr h)],
  simp [] [] [] ["[", expr this, "]"] [] []
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff
(x
 y : F) : «expr ↔ »(«expr = »(«expr / »(«expr⟪ , ⟫_ℝ»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), 1), «expr ∧ »(«expr ≠ »(x, 0), «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(0, r), «expr = »(y, «expr • »(r, x)))))) :=
begin
  split,
  { intro [ident h],
    have [ident ha] [] [":=", expr h],
    apply_fun [expr exprabsR()] ["at", ident ha] [],
    norm_num [] ["at", ident ha],
    rcases [expr (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hy, "⟩", "⟩", "⟩"],
    use ["[", expr hx, ",", expr r, "]"],
    refine [expr and.intro _ hy],
    by_contradiction [ident hrneg],
    rw [expr hy] ["at", ident h],
    rw [expr real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx (lt_of_le_of_ne (le_of_not_lt hrneg) hr)] ["at", ident h],
    norm_num [] ["at", ident h] },
  { intro [ident h],
    rcases [expr h, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hy, "⟩", "⟩", "⟩"],
    rw [expr hy] [],
    exact [expr real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff
(x
 y : F) : «expr ↔ »(«expr = »(«expr / »(«expr⟪ , ⟫_ℝ»(x, y), «expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y))), «expr- »(1)), «expr ∧ »(«expr ≠ »(x, 0), «expr∃ , »((r : exprℝ()), «expr ∧ »(«expr < »(r, 0), «expr = »(y, «expr • »(r, x)))))) :=
begin
  split,
  { intro [ident h],
    have [ident ha] [] [":=", expr h],
    apply_fun [expr exprabsR()] ["at", ident ha] [],
    norm_num [] ["at", ident ha],
    rcases [expr (abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hy, "⟩", "⟩", "⟩"],
    use ["[", expr hx, ",", expr r, "]"],
    refine [expr and.intro _ hy],
    by_contradiction [ident hrpos],
    rw [expr hy] ["at", ident h],
    rw [expr real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx (lt_of_le_of_ne (le_of_not_lt hrpos) hr.symm)] ["at", ident h],
    norm_num [] ["at", ident h] },
  { intro [ident h],
    rcases [expr h, "with", "⟨", ident hx, ",", "⟨", ident r, ",", "⟨", ident hr, ",", ident hy, "⟩", "⟩", "⟩"],
    rw [expr hy] [],
    exact [expr real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr] }
end

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff
{x
 y : E} : «expr ↔ »(«expr = »(«expr⟪ , ⟫»(x, y), «expr * »((«expr∥ ∥»(x) : 𝕜), «expr∥ ∥»(y))), «expr = »(«expr • »((«expr∥ ∥»(y) : 𝕜), x), «expr • »((«expr∥ ∥»(x) : 𝕜), y))) :=
begin
  by_cases [expr h, ":", expr «expr ∨ »(«expr = »(x, 0), «expr = »(y, 0))],
  { cases [expr h] []; simp [] [] [] ["[", expr h, "]"] [] [] },
  calc
    «expr ↔ »(«expr = »(«expr⟪ , ⟫»(x, y), «expr * »((«expr∥ ∥»(x) : 𝕜), «expr∥ ∥»(y))), «expr = »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)), re «expr⟪ , ⟫»(x, y))) : begin
      norm_cast [],
      split,
      { intros [ident h'],
        simp [] [] [] ["[", expr h', "]"] [] [] },
      { have [ident cauchy_schwarz] [] [":=", expr abs_inner_le_norm x y],
        intros [ident h'],
        rw [expr h'] ["at", "⊢", ident cauchy_schwarz],
        rwa [expr re_eq_self_of_le] [] }
    end
    «expr ↔ »(..., «expr = »(«expr * »(«expr * »(«expr * »(2, «expr∥ ∥»(x)), «expr∥ ∥»(y)), «expr - »(«expr * »(«expr∥ ∥»(x), «expr∥ ∥»(y)), re «expr⟪ , ⟫»(x, y))), 0)) : by simp [] [] [] ["[", expr h, ",", expr show «expr ≠ »((2 : exprℝ()), 0), by norm_num [] [], ",", expr sub_eq_zero, "]"] [] []
    «expr ↔ »(..., «expr = »(«expr * »(«expr∥ ∥»(«expr - »(«expr • »((«expr∥ ∥»(y) : 𝕜), x), «expr • »((«expr∥ ∥»(x) : 𝕜), y))), «expr∥ ∥»(«expr - »(«expr • »((«expr∥ ∥»(y) : 𝕜), x), «expr • »((«expr∥ ∥»(x) : 𝕜), y)))), 0)) : begin
      simp [] [] ["only"] ["[", expr norm_sub_mul_self, ",", expr inner_smul_left, ",", expr inner_smul_right, ",", expr norm_smul, ",", expr conj_of_real, ",", expr is_R_or_C.norm_eq_abs, ",", expr abs_of_real, ",", expr of_real_im, ",", expr of_real_re, ",", expr mul_re, ",", expr abs_norm_eq_norm, "]"] [] [],
      refine [expr eq.congr _ rfl],
      ring []
    end
    «expr ↔ »(..., «expr = »(«expr • »((«expr∥ ∥»(y) : 𝕜), x), «expr • »((«expr∥ ∥»(x) : 𝕜), y))) : by simp [] [] [] ["[", expr norm_sub_eq_zero_iff, "]"] [] []
end

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff_real {x y : F} : (⟪x, y⟫_ℝ = ∥x∥*∥y∥) ↔ ∥y∥ • x = ∥x∥ • y :=
  inner_eq_norm_mul_iff

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_norm_mul_iff_of_norm_one {x y : E} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) : ⟪x, y⟫ = 1 ↔ x = y :=
  by 
    convert inner_eq_norm_mul_iff using 2 <;> simp [hx, hy]

theorem inner_lt_norm_mul_iff_real {x y : F} : (⟪x, y⟫_ℝ < ∥x∥*∥y∥) ↔ ∥y∥ • x ≠ ∥x∥ • y :=
  calc (⟪x, y⟫_ℝ < ∥x∥*∥y∥) ↔ ⟪x, y⟫_ℝ ≠ ∥x∥*∥y∥ := ⟨ne_of_ltₓ, lt_of_le_of_neₓ (real_inner_le_norm _ _)⟩
    _ ↔ ∥y∥ • x ≠ ∥x∥ • y := not_congr inner_eq_norm_mul_iff_real
    

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) : ⟪x, y⟫_ℝ < 1 ↔ x ≠ y :=
  by 
    convert inner_lt_norm_mul_iff_real <;> simp [hx, hy]

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type _} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ} (v₁ : ι₁ → F)
  (h₁ : (∑i in s₁, w₁ i) = 0) {ι₂ : Type _} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ} (v₂ : ι₂ → F) (h₂ : (∑i in s₂, w₂ i) = 0) :
  ⟪∑i₁ in s₁, w₁ i₁ • v₁ i₁, ∑i₂ in s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
    (-∑i₁ in s₁, ∑i₂ in s₂, (w₁ i₁*w₂ i₂)*∥v₁ i₁ - v₂ i₂∥*∥v₁ i₁ - v₂ i₂∥) / 2 :=
  by 
    simpRw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
      real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ←div_sub_div_same, ←div_add_div_same,
      mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ←Finset.mul_sum,
      ←Finset.sum_mul, h₁, h₂, zero_mul, mul_zero, Finset.sum_const_zero, zero_addₓ, zero_sub, Finset.mul_sum, neg_div,
      Finset.sum_div, mul_div_assoc, mul_assocₓ]

/-- The inner product with a fixed left element, as a continuous linear map.  This can be upgraded
to a continuous map which is jointly conjugate-linear in the left argument and linear in the right
argument, once (TODO) conjugate-linear maps have been defined. -/
def innerRight (v : E) : E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous
    { toFun := fun w => ⟪v, w⟫, map_add' := fun x y => inner_add_right, map_smul' := fun c x => inner_smul_right } ∥v∥
    (by 
      simpa using norm_inner_le_norm v)

@[simp]
theorem inner_right_coe (v : E) : (innerRight v : E → 𝕜) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem inner_right_apply (v w : E) : innerRight v w = ⟪v, w⟫ :=
  rfl

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `is_bounded_bilinear_map`.

In order to state these results, we need a `normed_space ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `inner_product_space.is_R_or_C_to_real 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[normed_space ℝ E]` and `[is_scalar_tower ℝ 𝕜 E]`. In both interesting cases `𝕜 = ℝ` and `𝕜 = ℂ`
we have these instances.
-/
theorem is_bounded_bilinear_map_inner [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] :
  IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := fun _ _ _ => inner_add_left,
    smulLeft :=
      fun r x y =>
        by 
          simp only [←algebra_map_smul 𝕜 r x, algebra_map_eq_of_real, inner_smul_real_left],
    add_right := fun _ _ _ => inner_add_right,
    smulRight :=
      fun r x y =>
        by 
          simp only [←algebra_map_smul 𝕜 r y, algebra_map_eq_of_real, inner_smul_real_right],
    bound :=
      ⟨1, zero_lt_one,
        fun x y =>
          by 
            rw [one_mulₓ]
            exact norm_inner_le_norm x y⟩ }

end Norm

section BesselsInequality

variable {ι : Type _} (x : E) {v : ι → E}

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bessel's inequality for finite sums. -/
theorem orthonormal.sum_inner_products_le
{s : finset ι}
(hv : orthonormal 𝕜 v) : «expr ≤ »(«expr∑ in , »((i), s, «expr ^ »(«expr∥ ∥»(«expr⟪ , ⟫»(v i, x)), 2)), «expr ^ »(«expr∥ ∥»(x), 2)) :=
begin
  have [ident h₂] [":", expr «expr = »(«expr∑ in , »((i), s, «expr∑ in , »((j), s, «expr * »(«expr * »(«expr⟪ , ⟫»(v i, x), «expr⟪ , ⟫»(x, v j)), «expr⟪ , ⟫»(v j, v i)))), («expr∑ in , »((k), s, «expr * »(«expr⟪ , ⟫»(v k, x), «expr⟪ , ⟫»(x, v k))) : 𝕜))] [],
  { exact [expr hv.inner_left_right_finset] },
  have [ident h₃] [":", expr ∀ z : 𝕜, «expr = »(re «expr * »(z, exprconj() z), «expr ^ »(«expr∥ ∥»(z), 2))] [],
  { intro [ident z],
    simp [] [] ["only"] ["[", expr mul_conj, ",", expr norm_sq_eq_def', "]"] [] [],
    norm_cast [] },
  suffices [ident hbf] [":", expr «expr = »(«expr ^ »(«expr∥ ∥»(«expr - »(x, «expr∑ in , »((i), s, «expr • »(«expr⟪ , ⟫»(v i, x), v i)))), 2), «expr - »(«expr ^ »(«expr∥ ∥»(x), 2), «expr∑ in , »((i), s, «expr ^ »(«expr∥ ∥»(«expr⟪ , ⟫»(v i, x)), 2))))],
  { rw ["[", "<-", expr sub_nonneg, ",", "<-", expr hbf, "]"] [],
    simp [] [] ["only"] ["[", expr norm_nonneg, ",", expr pow_nonneg, "]"] [] [] },
  rw ["[", expr norm_sub_sq, ",", expr sub_add, "]"] [],
  simp [] [] ["only"] ["[", expr inner_product_space.norm_sq_eq_inner, ",", expr inner_sum, "]"] [] [],
  simp [] [] ["only"] ["[", expr sum_inner, ",", expr two_mul, ",", expr inner_smul_right, ",", expr inner_conj_sym, ",", "<-", expr mul_assoc, ",", expr h₂, ",", "<-", expr h₃, ",", expr inner_conj_sym, ",", expr add_monoid_hom.map_sum, ",", expr finset.mul_sum, ",", "<-", expr finset.sum_sub_distrib, ",", expr inner_smul_left, ",", expr add_sub_cancel', "]"] [] []
end

/-- Bessel's inequality. -/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) : (∑'i, ∥⟪v i, x⟫∥^2) ≤ (∥x∥^2) :=
  by 
    refine' tsum_le_of_sum_le' _ fun s => hv.sum_inner_products_le x 
    simp only [norm_nonneg, pow_nonneg]

/-- The sum defined in Bessel's inequality is summable. -/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) : Summable fun i => ∥⟪v i, x⟫∥^2 :=
  by 
    use ⨆s : Finset ι, ∑i in s, ∥⟪v i, x⟫∥^2
    apply has_sum_of_is_lub_of_nonneg
    ·
      intro b 
      simp only [norm_nonneg, pow_nonneg]
    ·
      refine' is_lub_csupr _ 
      use ∥x∥^2
      rintro y ⟨s, rfl⟩
      exact hv.sum_inner_products_le x

end BesselsInequality

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance IsROrC.innerProductSpace : InnerProductSpace 𝕜 𝕜 :=
  { inner := fun x y => conj x*y,
    norm_sq_eq_inner :=
      fun x =>
        by 
          unfold inner 
          rw [mul_commₓ, mul_conj, of_real_re, norm_sq_eq_def'],
    conj_sym :=
      fun x y =>
        by 
          simp [mul_commₓ],
    add_left :=
      fun x y z =>
        by 
          simp [inner, add_mulₓ],
    smulLeft :=
      fun x y z =>
        by 
          simp [inner, mul_assocₓ] }

@[simp]
theorem IsROrC.inner_apply (x y : 𝕜) : ⟪x, y⟫ = conj x*y :=
  rfl

/-! ### Inner product space structure on subspaces -/


/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  { Submodule.normedSpace W with inner := fun x y => ⟪(x : E), (y : E)⟫, conj_sym := fun _ _ => inner_conj_sym _ _,
    norm_sq_eq_inner := fun _ => norm_sq_eq_inner _, add_left := fun _ _ _ => inner_add_left,
    smulLeft := fun _ _ _ => inner_smul_left }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), «expr↑ » y⟫ :=
  rfl

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/


section OrthogonalFamily

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

open_locale DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`. -/
def OrthogonalFamily (V : ι → Submodule 𝕜 E) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ {v : E} hv : v ∈ V i {w : E} hw : w ∈ V j, ⟪v, w⟫ = 0

variable {𝕜} {V : ι → Submodule 𝕜 E}

include dec_ι

theorem OrthogonalFamily.eq_ite (hV : OrthogonalFamily 𝕜 V) {i j : ι} (v : V i) (w : V j) :
  ⟪(v : E), w⟫ = ite (i = j) ⟪(v : E), w⟫ 0 :=
  by 
    splitIfs
    ·
      rfl
    ·
      exact hV h v.prop w.prop

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orthogonal_family.inner_right_dfinsupp
(hV : orthogonal_family 𝕜 V)
(l : «exprΠ₀ , »((i), V i))
(i : ι)
(v : V i) : «expr = »(«expr⟪ , ⟫»((v : E), dfinsupp.lsum exprℕ() (λ i, (V i).subtype) l), «expr⟪ , ⟫»(v, l i)) :=
calc
  «expr = »(«expr⟪ , ⟫»((v : E), dfinsupp.lsum exprℕ() (λ
     i, (V i).subtype) l), l.sum (λ j, λ w, «expr⟪ , ⟫»((v : E), w))) : begin
    let [ident F] [":", expr «expr →+ »(E, 𝕜)] [":=", expr (@inner_right 𝕜 E _ _ v).to_linear_map.to_add_monoid_hom],
    have [ident hF] [] [":=", expr congr_arg add_monoid_hom.to_fun (dfinsupp.comp_sum_add_hom F (λ
       j, (V j).subtype.to_add_monoid_hom))],
    convert [] [expr congr_fun hF l] ["using", 1],
    simp [] [] ["only"] ["[", expr dfinsupp.sum_add_hom_apply, ",", expr continuous_linear_map.to_linear_map_eq_coe, ",", expr add_monoid_hom.coe_comp, ",", expr inner_right_coe, ",", expr add_monoid_hom.to_fun_eq_coe, ",", expr linear_map.to_add_monoid_hom_coe, ",", expr continuous_linear_map.coe_coe, "]"] [] [],
    congr
  end
  «expr = »(..., l.sum (λ
    j, λ
    w, ite «expr = »(i, j) «expr⟪ , ⟫»((v : E), w) 0)) : «expr $ »(congr_arg l.sum, «expr $ »(funext, λ
    j, «expr $ »(funext, hV.eq_ite v)))
  «expr = »(..., «expr⟪ , ⟫»(v, l i)) : begin
    simp [] [] ["only"] ["[", expr dfinsupp.sum, ",", expr submodule.coe_inner, ",", expr finset.sum_ite_eq, ",", expr ite_eq_left_iff, ",", expr dfinsupp.mem_support_to_fun, ",", expr not_not, "]"] [] [],
    intros [ident h],
    simp [] [] [] ["[", expr h, "]"] [] []
  end

omit dec_ι

theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (hV : OrthogonalFamily 𝕜 V) (l : ∀ i, V i) (i : ι) (v : V i) :
  ⟪(v : E), ∑j : ι, l j⟫ = ⟪v, l i⟫ :=
  calc ⟪(v : E), ∑j : ι, l j⟫ = ∑j : ι, ⟪(v : E), l j⟫ :=
    by 
      rw [inner_sum]
    _ = ∑j, ite (i = j) ⟪(v : E), l j⟫ 0 := congr_argₓ (Finset.sum Finset.univ)$ funext$ fun j => hV.eq_ite v (l j)
    _ = ⟪v, l i⟫ :=
    by 
      simp 
    

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem orthogonal_family.independent (hV : orthogonal_family 𝕜 V) : complete_lattice.independent V :=
begin
  apply [expr complete_lattice.independent_of_dfinsupp_lsum_injective],
  rw ["[", "<-", expr @linear_map.ker_eq_bot _ _ _ _ _ _ (direct_sum.add_comm_group (λ
     i, V i)), ",", expr submodule.eq_bot_iff, "]"] [],
  intros [ident v, ident hv],
  rw [expr linear_map.mem_ker] ["at", ident hv],
  ext [] [ident i] [],
  have [] [":", expr «expr = »(«expr⟪ , ⟫»((v i : E), dfinsupp.lsum exprℕ() (λ i, (V i).subtype) v), 0)] [],
  { simp [] [] [] ["[", expr hv, "]"] [] [] },
  simpa [] [] ["only"] ["[", expr submodule.coe_zero, ",", expr submodule.coe_eq_zero, ",", expr direct_sum.zero_apply, ",", expr inner_self_eq_zero, ",", expr hV.inner_right_dfinsupp, "]"] [] ["using", expr this]
end

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp (hV : OrthogonalFamily 𝕜 V) {γ : Type _} {f : γ → ι} (hf : Function.Injective f) :
  OrthogonalFamily 𝕜 (V ∘ f) :=
  fun i j hij v hv w hw => hV (hf.ne hij) hv hw

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem orthogonal_family.orthonormal_sigma_orthonormal
(hV : orthogonal_family 𝕜 V)
{α : ι → Type*}
{v_family : ∀ i, α i → V i}
(hv_family : ∀ i, orthonormal 𝕜 (v_family i)) : orthonormal 𝕜 (λ a : «exprΣ , »((i), α i), (v_family a.1 a.2 : E)) :=
begin
  split,
  { rintros ["⟨", ident i, ",", ident vi, "⟩"],
    exact [expr (hv_family i).1 vi] },
  rintros ["⟨", ident i, ",", ident vi, "⟩", "⟨", ident j, ",", ident vj, "⟩", ident hvij],
  by_cases [expr hij, ":", expr «expr = »(i, j)],
  { subst [expr hij],
    have [] [":", expr «expr ≠ »(vi, vj)] [":=", expr by simpa [] [] [] [] [] ["using", expr hvij]],
    exact [expr (hv_family i).2 this] },
  { exact [expr hV hij (v_family i vi : V i).prop (v_family j vj : V j).prop] }
end

include dec_ι

theorem DirectSum.SubmoduleIsInternal.collected_basis_orthonormal (hV : OrthogonalFamily 𝕜 V)
  (hV_sum : DirectSum.SubmoduleIsInternal V) {α : ι → Type _} {v_family : ∀ i, Basis (α i) 𝕜 (V i)}
  (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) : Orthonormal 𝕜 (hV_sum.collected_basis v_family) :=
  by 
    simpa using hV.orthonormal_sigma_orthonormal hv_family

omit dec_ι

end OrthogonalFamily

section IsROrCToReal

variable {G : Type _}

variable (𝕜 E)

include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def HasInner.isROrCToReal : HasInner ℝ E :=
  { inner := fun x y => re ⟪x, y⟫ }

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def InnerProductSpace.isROrCToReal : InnerProductSpace ℝ E :=
  { HasInner.isROrCToReal 𝕜 E, NormedSpace.restrictScalars ℝ 𝕜 E with norm_sq_eq_inner := norm_sq_eq_inner,
    conj_sym := fun x y => inner_re_symm,
    add_left :=
      fun x y z =>
        by 
          change re ⟪x+y, z⟫ = re ⟪x, z⟫+re ⟪y, z⟫
          simp [inner_add_left],
    smulLeft :=
      fun x y r =>
        by 
          change re ⟪(r : 𝕜) • x, y⟫ = r*re ⟪x, y⟫
          simp [inner_smul_left] }

variable {E}

theorem real_inner_eq_re_inner (x y : E) : @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x y = re ⟪x, y⟫ :=
  rfl

theorem real_inner_I_smul_self (x : E) : @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x ((I : 𝕜) • x) = 0 :=
  by 
    simp [real_inner_eq_re_inner, inner_smul_right]

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance InnerProductSpace.complexToReal [InnerProductSpace ℂ G] : InnerProductSpace ℝ G :=
  InnerProductSpace.isROrCToReal ℂ G

end IsROrCToReal

section Continuous

/-!
### Continuity of the inner product
-/


-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem continuous_inner : continuous (λ p : «expr × »(E, E), «expr⟪ , ⟫»(p.1, p.2)) :=
begin
  letI [] [":", expr inner_product_space exprℝ() E] [":=", expr inner_product_space.is_R_or_C_to_real 𝕜 E],
  letI [] [":", expr is_scalar_tower exprℝ() 𝕜 E] [":=", expr restrict_scalars.is_scalar_tower _ _ _],
  exact [expr is_bounded_bilinear_map_inner.continuous]
end

variable {α : Type _}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : tendsto f l (𝓝 x)) (hg : tendsto g l (𝓝 y)) :
  tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.Tendsto _).comp (hf.prod_mk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

include 𝕜

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
  ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  hf.inner hg

theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  hf.inner hg

theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun t => ⟪f t, g t⟫) s :=
  fun x hx => (hf x hx).inner (hg x hx)

theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuous_at.2$ fun x => hf.continuous_at.inner hg.continuous_at

end Continuous

section ReApplyInnerSelf

/-- Extract a real bilinear form from an operator `T`, by taking the pairing `λ x, re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫

theorem ContinuousLinearMap.re_apply_inner_self_apply (T : E →L[𝕜] E) (x : E) : T.re_apply_inner_self x = re ⟪T x, x⟫ :=
  rfl

theorem ContinuousLinearMap.re_apply_inner_self_continuous (T : E →L[𝕜] E) : Continuous T.re_apply_inner_self :=
  re_clm.Continuous.comp$ T.continuous.inner continuous_id

theorem ContinuousLinearMap.re_apply_inner_self_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
  T.re_apply_inner_self (c • x) = (∥c∥^2)*T.re_apply_inner_self x :=
  by 
    simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.re_apply_inner_self_apply, inner_smul_left,
      inner_smul_right, ←mul_assocₓ, mul_conj, norm_sq_eq_def', ←smul_re, Algebra.smul_def (∥c∥^2) ⟪T x, x⟫,
      algebra_map_eq_of_real]

end ReApplyInnerSelf

/-! ### The orthogonal complement -/


section Orthogonal

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def Submodule.orthogonal : Submodule 𝕜 E :=
  { Carrier := { v | ∀ u _ : u ∈ K, ⟪u, v⟫ = 0 }, zero_mem' := fun _ _ => inner_zero_right,
    add_mem' :=
      fun x y hx hy u hu =>
        by 
          rw [inner_add_right, hx u hu, hy u hu, add_zeroₓ],
    smul_mem' :=
      fun c x hx u hu =>
        by 
          rw [inner_smul_right, hx u hu, mul_zero] }

notation:1200 K "ᗮ" => Submodule.orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem Submodule.mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀ u _ : u ∈ K, ⟪u, v⟫ = 0 :=
  Iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem Submodule.mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀ u _ : u ∈ K, ⟪v, u⟫ = 0 :=
  by 
    simpRw [Submodule.mem_orthogonal, inner_eq_zero_sym]

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem Submodule.inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem Submodule.inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 :=
  by 
    rw [inner_eq_zero_sym] <;> exact Submodule.inner_right_of_mem_orthogonal hu hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_right_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜∙u)ᗮ) : ⟪u, v⟫ = 0 :=
  Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_left_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜∙u)ᗮ) : ⟪v, u⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hv

/-- A vector orthogonal to `u` lies in `(𝕜 ∙ u)ᗮ`. -/
theorem mem_orthogonal_singleton_of_inner_right (u : E) {v : E} (hv : ⟪u, v⟫ = 0) : v ∈ (𝕜∙u)ᗮ :=
  by 
    intro w hw 
    rw [Submodule.mem_span_singleton] at hw 
    obtain ⟨c, rfl⟩ := hw 
    simp [inner_smul_left, hv]

/-- A vector orthogonal to `u` lies in `(𝕜 ∙ u)ᗮ`. -/
theorem mem_orthogonal_singleton_of_inner_left (u : E) {v : E} (hv : ⟪v, u⟫ = 0) : v ∈ (𝕜∙u)ᗮ :=
  mem_orthogonal_singleton_of_inner_right u$ inner_eq_zero_sym.2 hv

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.inf_orthogonal_eq_bot : K⊓Kᗮ = ⊥ :=
  by 
    rw [Submodule.eq_bot_iff]
    intro x 
    rw [Submodule.mem_inf]
    exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.orthogonal_disjoint : Disjoint K Kᗮ :=
  by 
    simp [disjoint_iff, K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅v : K, (innerRight (v : E)).ker :=
  by 
    apply le_antisymmₓ
    ·
      rw [le_infi_iff]
      rintro ⟨v, hv⟩ w hw 
      simpa using hw _ hv
    ·
      intro v hv w hw 
      simp only [Submodule.mem_infi] at hv 
      exact hv ⟨w, hw⟩

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem Submodule.is_closed_orthogonal : IsClosed (Kᗮ : Set E) :=
  by 
    rw [orthogonal_eq_inter K]
    convert is_closed_Inter fun v : K => (innerRight (v : E)).is_closed_ker 
    simp 

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.is_closed_orthogonal.complete_space_coe

variable (𝕜 E)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem Submodule.orthogonal_gc :
  @GaloisConnection (Submodule 𝕜 E) (OrderDual$ Submodule 𝕜 E) _ _ Submodule.orthogonal Submodule.orthogonal :=
  fun K₁ K₂ =>
    ⟨fun h v hv u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu),
      fun h v hv u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).monotone_l h

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  Submodule.orthogonal_le (Submodule.orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
theorem Submodule.le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem Submodule.inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ⊓K₂ᗮ = (K₁⊔K₂)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem Submodule.infi_orthogonal {ι : Type _} (K : ι → Submodule 𝕜 E) : (⨅i, (K i)ᗮ) = (supr K)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem Submodule.Inf_orthogonal (s : Set$ Submodule 𝕜 E) : (⨅(K : _)(_ : K ∈ s), Kᗮ) = (Sup s)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_Sup.symm

@[simp]
theorem Submodule.top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ :=
  by 
    ext 
    rw [Submodule.mem_bot, Submodule.mem_orthogonal]
    exact
      ⟨fun h => inner_self_eq_zero.mp (h x Submodule.mem_top),
        by 
          rintro rfl 
          simp ⟩

@[simp]
theorem Submodule.bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ :=
  by 
    rw [←Submodule.top_orthogonal_eq_bot, eq_top_iff]
    exact Submodule.le_orthogonal_orthogonal ⊤

-- error in Analysis.InnerProductSpace.Basic: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem submodule.orthogonal_eq_top_iff : «expr ↔ »(«expr = »(«expr ᗮ»(K), «expr⊤»()), «expr = »(K, «expr⊥»())) :=
begin
  refine [expr ⟨_, by { rintro [ident rfl], exact [expr submodule.bot_orthogonal_eq_top] }⟩],
  intro [ident h],
  have [] [":", expr «expr = »(«expr ⊓ »(K, «expr ᗮ»(K)), «expr⊥»())] [":=", expr K.orthogonal_disjoint.eq_bot],
  rwa ["[", expr h, ",", expr inf_comm, ",", expr top_inf_eq, "]"] ["at", ident this]
end

end Orthogonal

/-! ### Self-adjoint operators -/


section IsSelfAdjoint

/-- A (not necessarily bounded) operator on an inner product space is self-adjoint, if for all
`x`, `y`, we have `⟪T x, y⟫ = ⟪x, T y⟫`. -/
def IsSelfAdjoint (T : E →ₗ[𝕜] E) : Prop :=
  ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫

/-- An operator `T` on a `ℝ`-inner product space is self-adjoint if and only if it is
`bilin_form.is_self_adjoint` with respect to the bilinear form given by the inner product. -/
theorem is_self_adjoint_iff_bilin_form (T : F →ₗ[ℝ] F) : IsSelfAdjoint T ↔ bilinFormOfRealInner.IsSelfAdjoint T :=
  by 
    simp [IsSelfAdjoint, BilinForm.IsSelfAdjoint, BilinForm.IsAdjointPair]

theorem IsSelfAdjoint.conj_inner_sym {T : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T) (x y : E) : conj ⟪T x, y⟫ = ⟪T y, x⟫ :=
  by 
    rw [hT x y, inner_conj_sym]

@[simp]
theorem IsSelfAdjoint.apply_clm {T : E →L[𝕜] E} (hT : IsSelfAdjoint (T : E →ₗ[𝕜] E)) (x y : E) : ⟪T x, y⟫ = ⟪x, T y⟫ :=
  hT x y

/-- For a self-adjoint operator `T`, the function `λ x, ⟪T x, x⟫` is real-valued. -/
@[simp]
theorem IsSelfAdjoint.coe_re_apply_inner_self_apply {T : E →L[𝕜] E} (hT : IsSelfAdjoint (T : E →ₗ[𝕜] E)) (x : E) :
  (T.re_apply_inner_self x : 𝕜) = ⟪T x, x⟫ :=
  by 
    suffices  : ∃ r : ℝ, ⟪T x, x⟫ = r
    ·
      obtain ⟨r, hr⟩ := this 
      simp [hr, T.re_apply_inner_self_apply]
    rw [←eq_conj_iff_real]
    exact hT.conj_inner_sym x x

/-- If a self-adjoint operator preserves a submodule, its restriction to that submodule is
self-adjoint. -/
theorem IsSelfAdjoint.restrict_invariant {T : E →ₗ[𝕜] E} (hT : IsSelfAdjoint T) {V : Submodule 𝕜 E}
  (hV : ∀ v _ : v ∈ V, T v ∈ V) : IsSelfAdjoint (T.restrict hV) :=
  fun v w => hT v w

end IsSelfAdjoint

