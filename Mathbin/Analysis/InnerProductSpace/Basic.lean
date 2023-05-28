/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis

! This file was ported from Lean 3 source module analysis.inner_product_space.basic
! leanprover-community/mathlib commit 0b7c740e25651db0ba63648fbae9f9d6f941e31b
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

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the set of assumptions
`[normed_add_comm_group E] [inner_product_space 𝕜 E] [complete_space E]`.

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

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

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

#print Inner /-
/-- Syntactic typeclass for types endowed with an inner product -/
class Inner (𝕜 E : Type _) where
  inner : E → E → 𝕜
#align has_inner Inner
-/

export Inner (inner)

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

#print InnerProductSpace /-
/-- An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `‖x‖^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class InnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] [NormedAddCommGroup E] extends
  NormedSpace 𝕜 E, Inner 𝕜 E where
  norm_sq_eq_inner : ∀ x : E, ‖x‖ ^ 2 = re (inner x x)
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
#align inner_product_space InnerProductSpace
-/

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


#print InnerProductSpace.Core /-
/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
@[nolint has_nonempty_instance]
structure InnerProductSpace.Core (𝕜 : Type _) (F : Type _) [IsROrC 𝕜] [AddCommGroup F]
  [Module 𝕜 F] extends Inner 𝕜 F where
  conj_symm : ∀ x y, conj (inner y x) = inner x y
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  definite : ∀ x, inner x x = 0 → x = 0
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y
#align inner_product_space.core InnerProductSpace.Core
-/

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

#print InnerProductSpace.toCore /-
/-- Define `inner_product_space.core` from `inner_product_space`. Defined to reuse lemmas about
`inner_product_space.core` for `inner_product_space`s. Note that the `has_norm` instance provided by
`inner_product_space.core.has_norm` is propositionally but not definitionally equal to the original
norm. -/
def InnerProductSpace.toCore [NormedAddCommGroup E] [c : InnerProductSpace 𝕜 E] :
    InnerProductSpace.Core 𝕜 E :=
  { c with
    nonneg_re := fun x => by rw [← InnerProductSpace.norm_sq_eq_inner]; apply sq_nonneg
    definite := fun x hx =>
      norm_eq_zero.1 <| pow_eq_zero <| by rw [InnerProductSpace.norm_sq_eq_inner x, hx, map_zero] }
#align inner_product_space.to_core InnerProductSpace.toCore
-/

namespace InnerProductSpace.Core

variable [AddCommGroup F] [Module 𝕜 F] [c : InnerProductSpace.Core 𝕜 F]

include c

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

-- mathport name: exprnorm_sqK
local notation "norm_sqK" => @IsROrC.normSq 𝕜 _

-- mathport name: exprreK
local notation "reK" => @IsROrC.re 𝕜 _

-- mathport name: exprext_iff
local notation "ext_iff" => @IsROrC.ext_iff 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

#print InnerProductSpace.Core.toInner' /-
/-- Inner product defined by the `inner_product_space.core` structure. We can't reuse
`inner_product_space.core.to_has_inner` because it takes `inner_product_space.core` as an explicit
argument. -/
def toInner' : Inner 𝕜 F :=
  c.toHasInner
#align inner_product_space.core.to_has_inner' InnerProductSpace.Core.toInner'
-/

attribute [local instance] to_has_inner'

#print InnerProductSpace.Core.normSq /-
/-- The norm squared function for `inner_product_space.core` structure. -/
def normSq (x : F) :=
  reK ⟪x, x⟫
#align inner_product_space.core.norm_sq InnerProductSpace.Core.normSq
-/

-- mathport name: exprnorm_sqF
local notation "norm_sqF" => @normSq 𝕜 F _ _ _ _

/- warning: inner_product_space.core.inner_conj_symm -> InnerProductSpace.Core.inner_conj_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_conj_symm InnerProductSpace.Core.inner_conj_symmₓ'. -/
theorem inner_conj_symm (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_symm x y
#align inner_product_space.core.inner_conj_symm InnerProductSpace.Core.inner_conj_symm

/- warning: inner_product_space.core.inner_self_nonneg -> InnerProductSpace.Core.inner_self_nonneg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_nonneg InnerProductSpace.Core.inner_self_nonnegₓ'. -/
theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _
#align inner_product_space.core.inner_self_nonneg InnerProductSpace.Core.inner_self_nonneg

/- warning: inner_product_space.core.inner_self_im -> InnerProductSpace.Core.inner_self_im is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_im InnerProductSpace.Core.inner_self_imₓ'. -/
theorem inner_self_im (x : F) : im ⟪x, x⟫ = 0 := by
  rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp [inner_conj_symm]
#align inner_product_space.core.inner_self_im InnerProductSpace.Core.inner_self_im

/- warning: inner_product_space.core.inner_add_left -> InnerProductSpace.Core.inner_add_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HAdd.hAdd.{u2, u2, u2} F F F (instHAdd.{u2} F (AddZeroClass.toHasAdd.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))) x y) z) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))))) x y) z) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y z))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_add_left InnerProductSpace.Core.inner_add_leftₓ'. -/
theorem inner_add_left (x y z : F) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _
#align inner_product_space.core.inner_add_left InnerProductSpace.Core.inner_add_left

/- warning: inner_product_space.core.inner_add_right -> InnerProductSpace.Core.inner_add_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (HAdd.hAdd.{u2, u2, u2} F F F (instHAdd.{u2} F (AddZeroClass.toHasAdd.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))) y z)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))))) y z)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_add_right InnerProductSpace.Core.inner_add_rightₓ'. -/
theorem inner_add_right (x y z : F) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add] <;> simp only [inner_conj_symm]
#align inner_product_space.core.inner_add_right InnerProductSpace.Core.inner_add_right

/- warning: inner_product_space.core.coe_norm_sq_eq_inner_self -> InnerProductSpace.Core.ofReal_normSq_eq_inner_self is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u1} 𝕜 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (InnerProductSpace.Core.normSq.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c x)) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x)
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u2} 𝕜 (IsROrC.ofReal.{u2} 𝕜 _inst_1 (InnerProductSpace.Core.normSq.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c x)) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x)
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.coe_norm_sq_eq_inner_self InnerProductSpace.Core.ofReal_normSq_eq_inner_selfₓ'. -/
theorem ofReal_normSq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ :=
  by
  rw [ext_iff]
  exact ⟨by simp only [of_real_re] <;> rfl, by simp only [inner_self_im, of_real_im]⟩
#align inner_product_space.core.coe_norm_sq_eq_inner_self InnerProductSpace.Core.ofReal_normSq_eq_inner_self

/- warning: inner_product_space.core.inner_re_symm -> InnerProductSpace.Core.inner_re_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_re_symm InnerProductSpace.Core.inner_re_symmₓ'. -/
theorem inner_re_symm (x y : F) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]
#align inner_product_space.core.inner_re_symm InnerProductSpace.Core.inner_re_symm

/- warning: inner_product_space.core.inner_im_symm -> InnerProductSpace.Core.inner_im_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_im_symm InnerProductSpace.Core.inner_im_symmₓ'. -/
theorem inner_im_symm (x y : F) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]
#align inner_product_space.core.inner_im_symm InnerProductSpace.Core.inner_im_symm

/- warning: inner_product_space.core.inner_smul_left -> InnerProductSpace.Core.inner_smul_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_smul_left InnerProductSpace.Core.inner_smul_leftₓ'. -/
theorem inner_smul_left (x y : F) {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _
#align inner_product_space.core.inner_smul_left InnerProductSpace.Core.inner_smul_left

/- warning: inner_product_space.core.inner_smul_right -> InnerProductSpace.Core.inner_smul_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) {r : 𝕜}, Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (SMul.smul.{u1, u2} 𝕜 F (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 F (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 F (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (AddCommMonoid.toAddMonoid.{u2} F (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)))) (Module.toMulActionWithZero.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2) _inst_3)))) r y)) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) r (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) {r : 𝕜}, Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (HSMul.hSMul.{u2, u1, u1} 𝕜 F F (instHSMul.{u2, u1} 𝕜 F (SMulZeroClass.toSMul.{u2, u1} 𝕜 F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 F (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 F (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2) _inst_3))))) r y)) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) r (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_smul_right InnerProductSpace.Core.inner_smul_rightₓ'. -/
theorem inner_smul_right (x y : F) {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left] <;>
    simp only [conj_conj, inner_conj_symm, RingHom.map_mul]
#align inner_product_space.core.inner_smul_right InnerProductSpace.Core.inner_smul_right

/- warning: inner_product_space.core.inner_zero_left -> InnerProductSpace.Core.inner_zero_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))))) x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))))) x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_zero_left InnerProductSpace.Core.inner_zero_leftₓ'. -/
theorem inner_zero_left (x : F) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left] <;>
    simp only [MulZeroClass.zero_mul, RingHom.map_zero]
#align inner_product_space.core.inner_zero_left InnerProductSpace.Core.inner_zero_left

/- warning: inner_product_space.core.inner_zero_right -> InnerProductSpace.Core.inner_zero_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2))))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2)))))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_zero_right InnerProductSpace.Core.inner_zero_rightₓ'. -/
theorem inner_zero_right (x : F) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left] <;> simp only [RingHom.map_zero]
#align inner_product_space.core.inner_zero_right InnerProductSpace.Core.inner_zero_right

/- warning: inner_product_space.core.inner_self_eq_zero -> InnerProductSpace.Core.inner_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) (Eq.{succ u2} F x (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (Eq.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_eq_zero InnerProductSpace.Core.inner_self_eq_zeroₓ'. -/
theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  ⟨c.definite _, by rintro rfl; exact inner_zero_left _⟩
#align inner_product_space.core.inner_self_eq_zero InnerProductSpace.Core.inner_self_eq_zero

/- warning: inner_product_space.core.norm_sq_eq_zero -> InnerProductSpace.Core.normSq_eq_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Eq.{1} Real (InnerProductSpace.Core.normSq.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u2} F x (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Eq.{1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : 𝕜) => Real) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x)) (InnerProductSpace.Core.normSq.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c x) (OfNat.ofNat.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : 𝕜) => Real) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x)) 0 (Zero.toOfNat0.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.403 : 𝕜) => Real) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x)) Real.instZeroReal))) (Eq.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.norm_sq_eq_zero InnerProductSpace.Core.normSq_eq_zeroₓ'. -/
theorem normSq_eq_zero {x : F} : norm_sqF x = 0 ↔ x = 0 :=
  Iff.trans
    (by simp only [norm_sq, ext_iff, map_zero, inner_self_im, eq_self_iff_true, and_true_iff])
    (@inner_self_eq_zero 𝕜 _ _ _ _ _ x)
#align inner_product_space.core.norm_sq_eq_zero InnerProductSpace.Core.normSq_eq_zero

/- warning: inner_product_space.core.inner_self_ne_zero -> InnerProductSpace.Core.inner_self_ne_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Ne.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) (Ne.{succ u2} F x (OfNat.ofNat.{u2} F 0 (OfNat.mk.{u2} F 0 (Zero.zero.{u2} F (AddZeroClass.toHasZero.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] {x : F}, Iff (Ne.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))))))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_ne_zero InnerProductSpace.Core.inner_self_ne_zeroₓ'. -/
theorem inner_self_ne_zero {x : F} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.Not
#align inner_product_space.core.inner_self_ne_zero InnerProductSpace.Core.inner_self_ne_zero

/- warning: inner_product_space.core.inner_self_re_to_K -> InnerProductSpace.Core.inner_self_ofReal_re is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_re_to_K InnerProductSpace.Core.inner_self_ofReal_reₓ'. -/
theorem inner_self_ofReal_re (x : F) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [ext_iff, inner_self_im]
#align inner_product_space.core.inner_self_re_to_K InnerProductSpace.Core.inner_self_ofReal_re

/- warning: inner_product_space.core.norm_inner_symm -> InnerProductSpace.Core.norm_inner_symm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{1} Real (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{1} Real (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.norm_inner_symm InnerProductSpace.Core.norm_inner_symmₓ'. -/
theorem norm_inner_symm (x y : F) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]
#align inner_product_space.core.norm_inner_symm InnerProductSpace.Core.norm_inner_symm

/- warning: inner_product_space.core.inner_neg_left -> InnerProductSpace.Core.inner_neg_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (Neg.neg.{u2} F (SubNegMonoid.toHasNeg.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2))) x) y) (Neg.neg.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))) x) y) (Neg.neg.{u2} 𝕜 (Ring.toNeg.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_neg_left InnerProductSpace.Core.inner_neg_leftₓ'. -/
theorem inner_neg_left (x y : F) : ⟪-x, y⟫ = -⟪x, y⟫ := by rw [← neg_one_smul 𝕜 x, inner_smul_left];
  simp
#align inner_product_space.core.inner_neg_left InnerProductSpace.Core.inner_neg_left

/- warning: inner_product_space.core.inner_neg_right -> InnerProductSpace.Core.inner_neg_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (Neg.neg.{u2} F (SubNegMonoid.toHasNeg.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2))) y)) (Neg.neg.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (Neg.neg.{u1} F (NegZeroClass.toNeg.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F _inst_2))))) y)) (Neg.neg.{u2} 𝕜 (Ring.toNeg.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_neg_right InnerProductSpace.Core.inner_neg_rightₓ'. -/
theorem inner_neg_right (x y : F) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left] <;> simp only [RingHom.map_neg, inner_conj_symm]
#align inner_product_space.core.inner_neg_right InnerProductSpace.Core.inner_neg_right

/- warning: inner_product_space.core.inner_sub_left -> InnerProductSpace.Core.inner_sub_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (SubNegMonoid.toHasSub.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))) x y) z) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))) x y) z) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y z))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_sub_left InnerProductSpace.Core.inner_sub_leftₓ'. -/
theorem inner_sub_left (x y z : F) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left, inner_neg_left]
#align inner_product_space.core.inner_sub_left InnerProductSpace.Core.inner_sub_left

/- warning: inner_product_space.core.inner_sub_right -> InnerProductSpace.Core.inner_sub_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (SubNegMonoid.toHasSub.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))) y z)) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F) (z : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))) y z)) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x z))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_sub_right InnerProductSpace.Core.inner_sub_rightₓ'. -/
theorem inner_sub_right (x y z : F) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right, inner_neg_right]
#align inner_product_space.core.inner_sub_right InnerProductSpace.Core.inner_sub_right

/- warning: inner_product_space.core.inner_mul_symm_re_eq_norm -> InnerProductSpace.Core.inner_mul_symm_re_eq_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_mul_symm_re_eq_norm InnerProductSpace.Core.inner_mul_symm_re_eq_normₓ'. -/
theorem inner_mul_symm_re_eq_norm (x y : F) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]; exact re_eq_norm_of_mul_conj (inner y x)
#align inner_product_space.core.inner_mul_symm_re_eq_norm InnerProductSpace.Core.inner_mul_symm_re_eq_norm

/- warning: inner_product_space.core.inner_add_add_self -> InnerProductSpace.Core.inner_add_add_self is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HAdd.hAdd.{u2, u2, u2} F F F (instHAdd.{u2} F (AddZeroClass.toHasAdd.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))) x y) (HAdd.hAdd.{u2, u2, u2} F F F (instHAdd.{u2} F (AddZeroClass.toHasAdd.{u2} F (AddMonoid.toAddZeroClass.{u2} F (SubNegMonoid.toAddMonoid.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))))) x y)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x)) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))))) x y) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))))) x y)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x)) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_add_add_self InnerProductSpace.Core.inner_add_add_selfₓ'. -/
/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self (x y : F) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right] <;> ring
#align inner_product_space.core.inner_add_add_self InnerProductSpace.Core.inner_add_add_self

/- warning: inner_product_space.core.inner_sub_sub_self -> InnerProductSpace.Core.inner_sub_sub_self is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (SubNegMonoid.toHasSub.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))) x y) (HSub.hSub.{u2, u2, u2} F F F (instHSub.{u2} F (SubNegMonoid.toHasSub.{u2} F (AddGroup.toSubNegMonoid.{u2} F (AddCommGroup.toAddGroup.{u2} F _inst_2)))) x y)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x)) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))) x y) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (AddCommGroup.toAddGroup.{u1} F _inst_2)))) x y)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x x) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y x)) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_sub_sub_self InnerProductSpace.Core.inner_sub_sub_selfₓ'. -/
-- Expand `inner (x - y) (x - y)`
theorem inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right] <;> ring
#align inner_product_space.core.inner_sub_sub_self InnerProductSpace.Core.inner_sub_sub_self

/- warning: inner_product_space.core.cauchy_schwarz_aux -> InnerProductSpace.Core.cauchy_schwarz_aux is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.cauchy_schwarz_aux InnerProductSpace.Core.cauchy_schwarz_auxₓ'. -/
/-- An auxiliary equality useful to prove the **Cauchy–Schwarz inequality**: the square of the norm
of `⟪x, y⟫ • x - ⟪x, x⟫ • y` is equal to `‖x‖ ^ 2 * (‖x‖ ^ 2 * ‖y‖ ^ 2 - ‖⟪x, y⟫‖ ^ 2)`. We use
`inner_product_space.of_core.norm_sq x` etc (defeq to `is_R_or_C.re ⟪x, x⟫`) instead of `‖x‖ ^ 2`
etc to avoid extra rewrites when applying it to an `inner_product_space`. -/
theorem cauchy_schwarz_aux (x y : F) :
    norm_sqF (⟪x, y⟫ • x - ⟪x, x⟫ • y) = norm_sqF x * (norm_sqF x * norm_sqF y - ‖⟪x, y⟫‖ ^ 2) :=
  by
  rw [← @of_real_inj 𝕜, coe_norm_sq_eq_inner_self]
  simp only [inner_sub_sub_self, inner_smul_left, inner_smul_right, conj_of_real, mul_sub, ←
    coe_norm_sq_eq_inner_self x, ← coe_norm_sq_eq_inner_self y]
  rw [← mul_assoc, mul_conj, IsROrC.conj_mul, norm_sq_eq_def', mul_left_comm, ← inner_conj_symm y,
    mul_conj, norm_sq_eq_def']
  push_cast
  ring
#align inner_product_space.core.cauchy_schwarz_aux InnerProductSpace.Core.cauchy_schwarz_aux

/- warning: inner_product_space.core.inner_mul_inner_self_le -> InnerProductSpace.Core.inner_mul_inner_self_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_mul_inner_self_le InnerProductSpace.Core.inner_mul_inner_self_leₓ'. -/
/-- **Cauchy–Schwarz inequality**.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le (x y : F) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp only [inner_zero_left, map_zero, MulZeroClass.zero_mul, norm_zero]
  · have hx' : 0 < norm_sqF x := inner_self_nonneg.lt_of_ne' (mt norm_sq_eq_zero.1 hx)
    rw [← sub_nonneg, ← mul_nonneg_iff_right_nonneg_of_pos hx', ← norm_sq, ← norm_sq,
      norm_inner_symm y, ← sq, ← cauchy_schwarz_aux]
    exact inner_self_nonneg
#align inner_product_space.core.inner_mul_inner_self_le InnerProductSpace.Core.inner_mul_inner_self_le

#print InnerProductSpace.Core.toNorm /-
/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def toNorm : Norm F where norm x := sqrt (re ⟪x, x⟫)
#align inner_product_space.core.to_has_norm InnerProductSpace.Core.toNorm
-/

attribute [local instance] to_has_norm

/- warning: inner_product_space.core.norm_eq_sqrt_inner -> InnerProductSpace.Core.norm_eq_sqrt_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.norm_eq_sqrt_inner InnerProductSpace.Core.norm_eq_sqrt_innerₓ'. -/
theorem norm_eq_sqrt_inner (x : F) : ‖x‖ = sqrt (re ⟪x, x⟫) :=
  rfl
#align inner_product_space.core.norm_eq_sqrt_inner InnerProductSpace.Core.norm_eq_sqrt_inner

/- warning: inner_product_space.core.inner_self_eq_norm_mul_norm -> InnerProductSpace.Core.inner_self_eq_norm_mul_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.inner_self_eq_norm_mul_norm InnerProductSpace.Core.inner_self_eq_norm_mul_normₓ'. -/
theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]
#align inner_product_space.core.inner_self_eq_norm_mul_norm InnerProductSpace.Core.inner_self_eq_norm_mul_norm

/- warning: inner_product_space.core.sqrt_norm_sq_eq_norm -> InnerProductSpace.Core.sqrt_normSq_eq_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{1} Real (Real.sqrt (InnerProductSpace.Core.normSq.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c x)) (Norm.norm.{u2} F (InnerProductSpace.Core.toNorm.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x)
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F), Eq.{1} Real (Real.sqrt (InnerProductSpace.Core.normSq.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c x)) (Norm.norm.{u1} F (InnerProductSpace.Core.toNorm.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x)
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.sqrt_norm_sq_eq_norm InnerProductSpace.Core.sqrt_normSq_eq_normₓ'. -/
theorem sqrt_normSq_eq_norm (x : F) : sqrt (norm_sqF x) = ‖x‖ :=
  rfl
#align inner_product_space.core.sqrt_norm_sq_eq_norm InnerProductSpace.Core.sqrt_normSq_eq_norm

/- warning: inner_product_space.core.norm_inner_le_norm -> InnerProductSpace.Core.norm_inner_le_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {F : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : AddCommGroup.{u2} F] [_inst_3 : Module.{u1, u2} 𝕜 F (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} F _inst_2)] [c : InnerProductSpace.Core.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 F (InnerProductSpace.Core.toInner'.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} F (InnerProductSpace.Core.toNorm.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) x) (Norm.norm.{u2} F (InnerProductSpace.Core.toNorm.{u1, u2} 𝕜 F _inst_1 _inst_2 _inst_3 c) y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {F : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : AddCommGroup.{u1} F] [_inst_3 : Module.{u2, u1} 𝕜 F (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} F _inst_2)] [c : InnerProductSpace.Core.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3] (x : F) (y : F), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 F (InnerProductSpace.Core.toInner'.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (InnerProductSpace.Core.toNorm.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) x) (Norm.norm.{u1} F (InnerProductSpace.Core.toNorm.{u2, u1} 𝕜 F _inst_1 _inst_2 _inst_3 c) y))
Case conversion may be inaccurate. Consider using '#align inner_product_space.core.norm_inner_le_norm InnerProductSpace.Core.norm_inner_le_normₓ'. -/
/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : F) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) <|
    calc
      ‖⟪x, y⟫‖ * ‖⟪x, y⟫‖ = ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ := by rw [norm_inner_symm]
      _ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := (inner_mul_inner_self_le x y)
      _ = ‖x‖ * ‖y‖ * (‖x‖ * ‖y‖) := by simp only [inner_self_eq_norm_mul_norm] <;> ring
      
#align inner_product_space.core.norm_inner_le_norm InnerProductSpace.Core.norm_inner_le_norm

#print InnerProductSpace.Core.toNormedAddCommGroup /-
/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def toNormedAddCommGroup : NormedAddCommGroup F :=
  AddGroupNorm.toNormedAddCommGroup
    { toFun := fun x => sqrt (re ⟪x, x⟫)
      map_zero' := by simp only [sqrt_zero, inner_zero_right, map_zero]
      neg' := fun x => by simp only [inner_neg_left, neg_neg, inner_neg_right]
      add_le' := fun x y =>
        by
        have h₁ : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ := norm_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ ‖⟪x, y⟫‖ := re_le_norm _
        have h₃ : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ := h₂.trans h₁
        have h₄ : re ⟪y, x⟫ ≤ ‖x‖ * ‖y‖ := by rwa [← inner_conj_symm, conj_re]
        have : ‖x + y‖ * ‖x + y‖ ≤ (‖x‖ + ‖y‖) * (‖x‖ + ‖y‖) :=
          by
          simp only [← inner_self_eq_norm_mul_norm, inner_add_add_self, mul_add, mul_comm, map_add]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this
      eq_zero_of_map_eq_zero' := fun x hx =>
        normSq_eq_zero.1 <| (sqrt_eq_zero inner_self_nonneg).1 hx }
#align inner_product_space.core.to_normed_add_comm_group InnerProductSpace.Core.toNormedAddCommGroup
-/

attribute [local instance] to_normed_add_comm_group

#print InnerProductSpace.Core.toNormedSpace /-
/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def toNormedSpace : NormedSpace 𝕜 F
    where norm_smul_le r x :=
    by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [IsROrC.conj_mul, of_real_mul_re, sqrt_mul, ← coe_norm_sq_eq_inner_self, of_real_re]
    · simp [sqrt_norm_sq_eq_norm, IsROrC.sqrt_normSq_eq_norm]
    · exact norm_sq_nonneg r
#align inner_product_space.core.to_normed_space InnerProductSpace.Core.toNormedSpace
-/

end InnerProductSpace.Core

section

attribute [local instance] InnerProductSpace.Core.toNormedAddCommGroup

#print InnerProductSpace.ofCore /-
/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space. The `normed_add_comm_group` structure is expected
to already be defined with `inner_product_space.of_core.to_normed_add_comm_group`. -/
def InnerProductSpace.ofCore [AddCommGroup F] [Module 𝕜 F] (c : InnerProductSpace.Core 𝕜 F) :
    InnerProductSpace 𝕜 F :=
  letI : NormedSpace 𝕜 F := @InnerProductSpace.Core.toNormedSpace 𝕜 F _ _ _ c
  { c with
    norm_sq_eq_inner := fun x =>
      by
      have h₁ : ‖x‖ ^ 2 = sqrt (re (c.inner x x)) ^ 2 := rfl
      have h₂ : 0 ≤ re (c.inner x x) := InnerProductSpace.Core.inner_self_nonneg
      simp [h₁, sq_sqrt, h₂] }
#align inner_product_space.of_core InnerProductSpace.ofCore
-/

end

/-! ### Properties of inner product spaces -/


variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

variable [NormedAddCommGroup F] [InnerProductSpace ℝ F]

variable [dec_E : DecidableEq E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- mathport name: exprIK
local notation "IK" => @IsROrC.i 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_inner)

section BasicProperties

/- warning: inner_conj_symm -> inner_conj_symm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (_x : RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) => 𝕜 -> 𝕜) (RingHom.hasCoeToFun.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (starRingEnd.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u1} 𝕜 _inst_1)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (FunLike.coe.{succ u2, succ u2, succ u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 (fun (_x : 𝕜) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) _x) (MulHomClass.toFunLike.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonUnitalNonAssocSemiring.toMul.{u2} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (NonUnitalNonAssocSemiring.toMul.{u2} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (NonUnitalRingHomClass.toMulHomClass.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) (RingHomClass.toNonUnitalRingHomClass.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (RingHom.instRingHomClassRingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (starRingEnd.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u2} 𝕜 _inst_1)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)
Case conversion may be inaccurate. Consider using '#align inner_conj_symm inner_conj_symmₓ'. -/
@[simp]
theorem inner_conj_symm (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_symm _ _
#align inner_conj_symm inner_conj_symm

#print real_inner_comm /-
theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_symm ℝ _ _ _ _ x y
#align real_inner_comm real_inner_comm
-/

/- warning: inner_eq_zero_symm -> inner_eq_zero_symm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, Iff (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))
Case conversion may be inaccurate. Consider using '#align inner_eq_zero_symm inner_eq_zero_symmₓ'. -/
theorem inner_eq_zero_symm {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 := by rw [← inner_conj_symm];
  exact star_eq_zero
#align inner_eq_zero_symm inner_eq_zero_symm

/- warning: inner_self_im -> inner_self_im is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_im inner_self_imₓ'. -/
@[simp]
theorem inner_self_im (x : E) : im ⟪x, x⟫ = 0 := by rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp
#align inner_self_im inner_self_im

/- warning: inner_add_left -> inner_add_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y) z) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x z) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y) z) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x z) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y z))
Case conversion may be inaccurate. Consider using '#align inner_add_left inner_add_leftₓ'. -/
theorem inner_add_left (x y z : E) : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _
#align inner_add_left inner_add_left

/- warning: inner_add_right -> inner_add_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) y z)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) y z)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x z))
Case conversion may be inaccurate. Consider using '#align inner_add_right inner_add_rightₓ'. -/
theorem inner_add_right (x y z : E) : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_symm, inner_add_left, RingHom.map_add]; simp only [inner_conj_symm]
#align inner_add_right inner_add_right

/- warning: inner_re_symm -> inner_re_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_re_symm inner_re_symmₓ'. -/
theorem inner_re_symm (x y : E) : re ⟪x, y⟫ = re ⟪y, x⟫ := by rw [← inner_conj_symm, conj_re]
#align inner_re_symm inner_re_symm

/- warning: inner_im_symm -> inner_im_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_im_symm inner_im_symmₓ'. -/
theorem inner_im_symm (x y : E) : im ⟪x, y⟫ = -im ⟪y, x⟫ := by rw [← inner_conj_symm, conj_im]
#align inner_im_symm inner_im_symm

/- warning: inner_smul_left -> inner_smul_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_smul_left inner_smul_leftₓ'. -/
theorem inner_smul_left (x y : E) (r : 𝕜) : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  InnerProductSpace.smul_left _ _ _
#align inner_smul_left inner_smul_left

/- warning: real_inner_smul_left -> real_inner_smul_left is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x) y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x) y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))
Case conversion may be inaccurate. Consider using '#align real_inner_smul_left real_inner_smul_leftₓ'. -/
theorem real_inner_smul_left (x y : F) (r : ℝ) : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left _ _ _
#align real_inner_smul_left real_inner_smul_left

/- warning: inner_smul_real_left -> inner_smul_real_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : Real), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) r) x) y) (SMul.smul.{0, u1} Real 𝕜 (SMulZeroClass.toHasSmul.{0, u1} Real 𝕜 (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real 𝕜 (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real 𝕜 (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (Module.toMulActionWithZero.{0, u1} Real 𝕜 (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (NormedSpace.toModule.{0, u1} Real 𝕜 Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NormedAlgebra.toNormedSpace'.{0, u1} Real Real.normedField 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))) (IsROrC.toNormedAlgebra.{u1} 𝕜 _inst_1))))))) r (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : Real), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HSMul.hSMul.{u2, u1, u1} 𝕜 E E (instHSMul.{u2, u1} 𝕜 E (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))))) (IsROrC.ofReal.{u2} 𝕜 _inst_1 r) x) y) (HSMul.hSMul.{0, u2, u2} Real 𝕜 𝕜 (instHSMul.{0, u2} Real 𝕜 (Algebra.toSMul.{0, u2} Real 𝕜 Real.instCommSemiringReal (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (NormedAlgebra.toAlgebra.{0, u2} Real 𝕜 Real.normedField (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (IsROrC.toNormedAlgebra.{u2} 𝕜 _inst_1)))) r (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align inner_smul_real_left inner_smul_real_leftₓ'. -/
theorem inner_smul_real_left (x y : E) (r : ℝ) : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_of_real, Algebra.smul_def]; rfl
#align inner_smul_real_left inner_smul_real_left

/- warning: inner_smul_right -> inner_smul_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : 𝕜), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) r y)) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) r (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : 𝕜), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (HSMul.hSMul.{u2, u1, u1} 𝕜 E E (instHSMul.{u2, u1} 𝕜 E (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))))) r y)) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) r (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align inner_smul_right inner_smul_rightₓ'. -/
theorem inner_smul_right (x y : E) (r : 𝕜) : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_symm]
#align inner_smul_right inner_smul_right

/- warning: real_inner_smul_right -> real_inner_smul_right is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))
Case conversion may be inaccurate. Consider using '#align real_inner_smul_right real_inner_smul_rightₓ'. -/
theorem real_inner_smul_right (x y : F) (r : ℝ) : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right _ _ _
#align real_inner_smul_right real_inner_smul_right

/- warning: inner_smul_real_right -> inner_smul_real_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : Real), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) r) y)) (SMul.smul.{0, u1} Real 𝕜 (SMulZeroClass.toHasSmul.{0, u1} Real 𝕜 (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real 𝕜 (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))))))) (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real 𝕜 (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField))))) (AddZeroClass.toHasZero.{u1} 𝕜 (AddMonoid.toAddZeroClass.{u1} 𝕜 (AddCommMonoid.toAddMonoid.{u1} 𝕜 (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (Module.toMulActionWithZero.{0, u1} Real 𝕜 (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real Real.normedField)))) (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (SeminormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (NormedSpace.toModule.{0, u1} Real 𝕜 Real.normedField (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NormedAlgebra.toNormedSpace'.{0, u1} Real Real.normedField 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))) (IsROrC.toNormedAlgebra.{u1} 𝕜 _inst_1))))))) r (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (r : Real), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (HSMul.hSMul.{u2, u1, u1} 𝕜 E E (instHSMul.{u2, u1} 𝕜 E (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))))) (IsROrC.ofReal.{u2} 𝕜 _inst_1 r) y)) (HSMul.hSMul.{0, u2, u2} Real 𝕜 𝕜 (instHSMul.{0, u2} Real 𝕜 (Algebra.toSMul.{0, u2} Real 𝕜 Real.instCommSemiringReal (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (NormedAlgebra.toAlgebra.{0, u2} Real 𝕜 Real.normedField (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (IsROrC.toNormedAlgebra.{u2} 𝕜 _inst_1)))) r (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align inner_smul_real_right inner_smul_real_rightₓ'. -/
theorem inner_smul_real_right (x y : E) (r : ℝ) : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]; rfl
#align inner_smul_real_right inner_smul_real_right

#print sesqFormOfInner /-
/-- The inner product as a sesquilinear form.

Note that in the case `𝕜 = ℝ` this is a bilinear form. -/
@[simps]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫)
    (fun x y z => inner_add_right _ _ _) (fun r x y => inner_smul_right _ _ _)
    (fun x y z => inner_add_left _ _ _) fun r x y => inner_smul_left _ _ _
#align sesq_form_of_inner sesqFormOfInner
-/

#print bilinFormOfRealInner /-
/-- The real inner product as a bilinear form. -/
@[simps]
def bilinFormOfRealInner : BilinForm ℝ F
    where
  bilin := inner
  bilin_add_left := inner_add_left
  bilin_smul_left a x y := inner_smul_left _ _ _
  bilin_add_right := inner_add_right
  bilin_smul_right a x y := inner_smul_right _ _ _
#align bilin_form_of_real_inner bilinFormOfRealInner
-/

/- warning: sum_inner -> sum_inner is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> E) (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Finset.sum.{u2, u3} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) s (fun (i : ι) => f i)) x) (Finset.sum.{u1, u3} 𝕜 ι (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) s (fun (i : ι) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f i) x))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> E) (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Finset.sum.{u1, u3} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) s (fun (i : ι) => f i)) x) (Finset.sum.{u2, u3} 𝕜 ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) s (fun (i : ι) => Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (f i) x))
Case conversion may be inaccurate. Consider using '#align sum_inner sum_innerₓ'. -/
/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
  (sesqFormOfInner x).map_sum
#align sum_inner sum_inner

/- warning: inner_sum -> inner_sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> E) (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (Finset.sum.{u2, u3} E ι (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) s (fun (i : ι) => f i))) (Finset.sum.{u1, u3} 𝕜 ι (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) s (fun (i : ι) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (f i)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (s : Finset.{u3} ι) (f : ι -> E) (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (Finset.sum.{u1, u3} E ι (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) s (fun (i : ι) => f i))) (Finset.sum.{u2, u3} 𝕜 ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) s (fun (i : ι) => Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (f i)))
Case conversion may be inaccurate. Consider using '#align inner_sum inner_sumₓ'. -/
/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) :
    ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
  (LinearMap.flip sesqFormOfInner x).map_sum
#align inner_sum inner_sum

/- warning: finsupp.sum_inner -> Finsupp.sum_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finsupp.sum_inner Finsupp.sum_innerₓ'. -/
/-- An inner product with a sum on the left, `finsupp` version. -/
theorem Finsupp.sum_inner {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪l.Sum fun (i : ι) (a : 𝕜) => a • v i, x⟫ = l.Sum fun (i : ι) (a : 𝕜) => conj a • ⟪v i, x⟫ :=
  by
  convert sum_inner l.support (fun a => l a • v a) x
  simp only [inner_smul_left, Finsupp.sum, smul_eq_mul]
#align finsupp.sum_inner Finsupp.sum_inner

/- warning: finsupp.inner_sum -> Finsupp.inner_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align finsupp.inner_sum Finsupp.inner_sumₓ'. -/
/-- An inner product with a sum on the right, `finsupp` version. -/
theorem Finsupp.inner_sum {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪x, l.Sum fun (i : ι) (a : 𝕜) => a • v i⟫ = l.Sum fun (i : ι) (a : 𝕜) => a • ⟪x, v i⟫ :=
  by
  convert inner_sum l.support (fun a => l a • v a) x
  simp only [inner_smul_right, Finsupp.sum, smul_eq_mul]
#align finsupp.inner_sum Finsupp.inner_sum

/- warning: dfinsupp.sum_inner -> Dfinsupp.sum_inner is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [dec : DecidableEq.{succ u3} ι] {α : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddZeroClass.{u4} (α i)] [_inst_7 : forall (i : ι) (x : α i), Decidable (Ne.{succ u4} (α i) x (OfNat.ofNat.{u4} (α i) 0 (OfNat.mk.{u4} (α i) 0 (Zero.zero.{u4} (α i) (AddZeroClass.toHasZero.{u4} (α i) (_inst_6 i))))))] (f : forall (i : ι), (α i) -> E) (l : Dfinsupp.{u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i))) (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Dfinsupp.sum.{u3, u4, u2} ι E (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) l f) x) (Dfinsupp.sum.{u3, u4, u1} ι 𝕜 (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) l (fun (i : ι) (a : α i) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (f i a) x))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u4}} [dec : DecidableEq.{succ u4} ι] {α : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddZeroClass.{u3} (α i)] [_inst_7 : forall (i : ι) (x : α i), Decidable (Ne.{succ u3} (α i) x (OfNat.ofNat.{u3} (α i) 0 (Zero.toOfNat0.{u3} (α i) (AddZeroClass.toZero.{u3} (α i) (_inst_6 i)))))] (f : forall (i : ι), (α i) -> E) (l : Dfinsupp.{u4, u3} ι (fun (i : ι) => α i) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i))) (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Dfinsupp.sum.{u4, u3, u1} ι E (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) l f) x) (Dfinsupp.sum.{u4, u3, u2} ι 𝕜 (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) l (fun (i : ι) (a : α i) => Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (f i a) x))
Case conversion may be inaccurate. Consider using '#align dfinsupp.sum_inner Dfinsupp.sum_innerₓ'. -/
theorem Dfinsupp.sum_inner {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪l.Sum f, x⟫ = l.Sum fun i a => ⟪f i a, x⟫ := by
  simp (config := { contextual := true }) only [Dfinsupp.sum, sum_inner, smul_eq_mul]
#align dfinsupp.sum_inner Dfinsupp.sum_inner

/- warning: dfinsupp.inner_sum -> Dfinsupp.inner_sum is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [dec : DecidableEq.{succ u3} ι] {α : ι -> Type.{u4}} [_inst_6 : forall (i : ι), AddZeroClass.{u4} (α i)] [_inst_7 : forall (i : ι) (x : α i), Decidable (Ne.{succ u4} (α i) x (OfNat.ofNat.{u4} (α i) 0 (OfNat.mk.{u4} (α i) 0 (Zero.zero.{u4} (α i) (AddZeroClass.toHasZero.{u4} (α i) (_inst_6 i))))))] (f : forall (i : ι), (α i) -> E) (l : Dfinsupp.{u3, u4} ι (fun (i : ι) => α i) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i))) (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (Dfinsupp.sum.{u3, u4, u2} ι E (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) l f)) (Dfinsupp.sum.{u3, u4, u1} ι 𝕜 (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toHasZero.{u4} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) l (fun (i : ι) (a : α i) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (f i a)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u4}} [dec : DecidableEq.{succ u4} ι] {α : ι -> Type.{u3}} [_inst_6 : forall (i : ι), AddZeroClass.{u3} (α i)] [_inst_7 : forall (i : ι) (x : α i), Decidable (Ne.{succ u3} (α i) x (OfNat.ofNat.{u3} (α i) 0 (Zero.toOfNat0.{u3} (α i) (AddZeroClass.toZero.{u3} (α i) (_inst_6 i)))))] (f : forall (i : ι), (α i) -> E) (l : Dfinsupp.{u4, u3} ι (fun (i : ι) => α i) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i))) (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (Dfinsupp.sum.{u4, u3, u1} ι E (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) l f)) (Dfinsupp.sum.{u4, u3, u2} ι 𝕜 (fun (i : ι) => α i) (fun (a : ι) (b : ι) => dec a b) (fun (i : ι) => AddZeroClass.toZero.{u3} ((fun (i : ι) => α i) i) (_inst_6 i)) (fun (i : ι) (x : α i) => _inst_7 i x) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) l (fun (i : ι) (a : α i) => Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (f i a)))
Case conversion may be inaccurate. Consider using '#align dfinsupp.inner_sum Dfinsupp.inner_sumₓ'. -/
theorem Dfinsupp.inner_sum {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _}
    [∀ i, AddZeroClass (α i)] [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E)
    (l : Π₀ i, α i) (x : E) : ⟪x, l.Sum f⟫ = l.Sum fun i a => ⟪x, f i a⟫ := by
  simp (config := { contextual := true }) only [Dfinsupp.sum, inner_sum, smul_eq_mul]
#align dfinsupp.inner_sum Dfinsupp.inner_sum

/- warning: inner_zero_left -> inner_zero_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))) x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))) x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inner_zero_left inner_zero_leftₓ'. -/
@[simp]
theorem inner_zero_left (x : E) : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, MulZeroClass.zero_mul]
#align inner_zero_left inner_zero_left

/- warning: inner_re_zero_left -> inner_re_zero_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_re_zero_left inner_re_zero_leftₓ'. -/
theorem inner_re_zero_left (x : E) : re ⟪0, x⟫ = 0 := by
  simp only [inner_zero_left, AddMonoidHom.map_zero]
#align inner_re_zero_left inner_re_zero_left

/- warning: inner_zero_right -> inner_zero_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2))))))))) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))
Case conversion may be inaccurate. Consider using '#align inner_zero_right inner_zero_rightₓ'. -/
@[simp]
theorem inner_zero_right (x : E) : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_symm, inner_zero_left, RingHom.map_zero]
#align inner_zero_right inner_zero_right

/- warning: inner_re_zero_right -> inner_re_zero_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_re_zero_right inner_re_zero_rightₓ'. -/
theorem inner_re_zero_right (x : E) : re ⟪x, 0⟫ = 0 := by
  simp only [inner_zero_right, AddMonoidHom.map_zero]
#align inner_re_zero_right inner_re_zero_right

/- warning: inner_self_nonneg -> inner_self_nonneg is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_nonneg inner_self_nonnegₓ'. -/
theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ :=
  InnerProductSpace.toCore.nonneg_re x
#align inner_self_nonneg inner_self_nonneg

/- warning: real_inner_self_nonneg -> real_inner_self_nonneg is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F}, LE.le.{0} Real Real.hasLe (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F}, LE.le.{0} Real Real.instLEReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)
Case conversion may be inaccurate. Consider using '#align real_inner_self_nonneg real_inner_self_nonnegₓ'. -/
theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ _ x
#align real_inner_self_nonneg real_inner_self_nonneg

/- warning: inner_self_re_to_K -> inner_self_ofReal_re is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_re_to_K inner_self_ofReal_reₓ'. -/
@[simp]
theorem inner_self_ofReal_re (x : E) : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ :=
  ((IsROrC.is_real_TFAE (⟪x, x⟫ : 𝕜)).out 2 3).2 (inner_self_im _)
#align inner_self_re_to_K inner_self_ofReal_re

/- warning: inner_self_eq_norm_sq_to_K -> inner_self_eq_norm_sq_to_K is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (HPow.hPow.{u1, 0, u1} 𝕜 Nat 𝕜 (instHPow.{u1, 0} 𝕜 Nat (Monoid.Pow.{u1} 𝕜 (Ring.toMonoid.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (HPow.hPow.{u2, 0, u2} 𝕜 Nat 𝕜 (instHPow.{u2, 0} 𝕜 Nat (Monoid.Pow.{u2} 𝕜 (MonoidWithZero.toMonoid.{u2} 𝕜 (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (IsROrC.ofReal.{u2} 𝕜 _inst_1 (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align inner_self_eq_norm_sq_to_K inner_self_eq_norm_sq_to_Kₓ'. -/
theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (‖x‖ ^ 2 : 𝕜) := by
  rw [← inner_self_ofReal_re, ← norm_sq_eq_inner, of_real_pow]
#align inner_self_eq_norm_sq_to_K inner_self_eq_norm_sq_to_K

/- warning: inner_self_re_eq_norm -> inner_self_re_eq_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_re_eq_norm inner_self_re_eq_normₓ'. -/
theorem inner_self_re_eq_norm (x : E) : re ⟪x, x⟫ = ‖⟪x, x⟫‖ :=
  by
  conv_rhs => rw [← inner_self_ofReal_re]
  symm
  exact norm_of_nonneg inner_self_nonneg
#align inner_self_re_eq_norm inner_self_re_eq_norm

/- warning: inner_self_norm_to_K -> inner_self_ofReal_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u1} 𝕜 ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u2} 𝕜 (IsROrC.ofReal.{u2} 𝕜 _inst_1 (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x)
Case conversion may be inaccurate. Consider using '#align inner_self_norm_to_K inner_self_ofReal_normₓ'. -/
theorem inner_self_ofReal_norm (x : E) : (‖⟪x, x⟫‖ : 𝕜) = ⟪x, x⟫ := by rw [← inner_self_re_eq_norm];
  exact inner_self_ofReal_re _
#align inner_self_norm_to_K inner_self_ofReal_norm

/- warning: real_inner_self_abs -> real_inner_self_abs is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x)
Case conversion may be inaccurate. Consider using '#align real_inner_self_abs real_inner_self_absₓ'. -/
theorem real_inner_self_abs (x : F) : |⟪x, x⟫_ℝ| = ⟪x, x⟫_ℝ :=
  @inner_self_ofReal_norm ℝ F _ _ _ x
#align real_inner_self_abs real_inner_self_abs

/- warning: inner_self_eq_zero -> inner_self_eq_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E}, Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) (Eq.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E}, Iff (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (Eq.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align inner_self_eq_zero inner_self_eq_zeroₓ'. -/
@[simp]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  rw [inner_self_eq_norm_sq_to_K, sq_eq_zero_iff, of_real_eq_zero, norm_eq_zero]
#align inner_self_eq_zero inner_self_eq_zero

/- warning: inner_self_ne_zero -> inner_self_ne_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E}, Iff (Ne.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E}, Iff (Ne.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) (Ne.{succ u1} E x (OfNat.ofNat.{u1} E 0 (Zero.toOfNat0.{u1} E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align inner_self_ne_zero inner_self_ne_zeroₓ'. -/
theorem inner_self_ne_zero {x : E} : ⟪x, x⟫ ≠ 0 ↔ x ≠ 0 :=
  inner_self_eq_zero.Not
#align inner_self_ne_zero inner_self_ne_zero

/- warning: inner_self_nonpos -> inner_self_nonpos is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_nonpos inner_self_nonposₓ'. -/
@[simp]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  rw [← norm_sq_eq_inner, (sq_nonneg _).le_iff_eq, sq_eq_zero_iff, norm_eq_zero]
#align inner_self_nonpos inner_self_nonpos

/- warning: real_inner_self_nonpos -> real_inner_self_nonpos is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F}, Iff (LE.le.{0} Real Real.hasLe (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F}, Iff (LE.le.{0} Real Real.instLEReal (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))))))
Case conversion may be inaccurate. Consider using '#align real_inner_self_nonpos real_inner_self_nonposₓ'. -/
theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 :=
  @inner_self_nonpos ℝ F _ _ _ x
#align real_inner_self_nonpos real_inner_self_nonpos

/- warning: norm_inner_symm -> norm_inner_symm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} Real (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y x))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} Real (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x))
Case conversion may be inaccurate. Consider using '#align norm_inner_symm norm_inner_symmₓ'. -/
theorem norm_inner_symm (x y : E) : ‖⟪x, y⟫‖ = ‖⟪y, x⟫‖ := by rw [← inner_conj_symm, norm_conj]
#align norm_inner_symm norm_inner_symm

/- warning: inner_neg_left -> inner_neg_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Neg.neg.{u2} E (SubNegMonoid.toHasNeg.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))) x) y) (Neg.neg.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Neg.neg.{u1} E (NegZeroClass.toNeg.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) x) y) (Neg.neg.{u2} 𝕜 (Ring.toNeg.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align inner_neg_left inner_neg_leftₓ'. -/
@[simp]
theorem inner_neg_left (x y : E) : ⟪-x, y⟫ = -⟪x, y⟫ := by rw [← neg_one_smul 𝕜 x, inner_smul_left];
  simp
#align inner_neg_left inner_neg_left

/- warning: inner_neg_right -> inner_neg_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (Neg.neg.{u2} E (SubNegMonoid.toHasNeg.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))) y)) (Neg.neg.{u1} 𝕜 (SubNegMonoid.toHasNeg.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (Neg.neg.{u1} E (NegZeroClass.toNeg.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) y)) (Neg.neg.{u2} 𝕜 (Ring.toNeg.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y))
Case conversion may be inaccurate. Consider using '#align inner_neg_right inner_neg_rightₓ'. -/
@[simp]
theorem inner_neg_right (x y : E) : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_symm, inner_neg_left] <;> simp only [RingHom.map_neg, inner_conj_symm]
#align inner_neg_right inner_neg_right

/- warning: inner_neg_neg -> inner_neg_neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Neg.neg.{u2} E (SubNegMonoid.toHasNeg.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))) x) (Neg.neg.{u2} E (SubNegMonoid.toHasNeg.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))) y)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (Neg.neg.{u1} E (NegZeroClass.toNeg.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) x) (Neg.neg.{u1} E (NegZeroClass.toNeg.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) y)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)
Case conversion may be inaccurate. Consider using '#align inner_neg_neg inner_neg_negₓ'. -/
theorem inner_neg_neg (x y : E) : ⟪-x, -y⟫ = ⟪x, y⟫ := by simp
#align inner_neg_neg inner_neg_neg

/- warning: inner_self_conj -> inner_self_conj is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u1} 𝕜 (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (_x : RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) => 𝕜 -> 𝕜) (RingHom.hasCoeToFun.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (starRingEnd.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u1} 𝕜 _inst_1)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{succ u2} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x)) (FunLike.coe.{succ u2, succ u2, succ u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 (fun (_x : 𝕜) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) _x) (MulHomClass.toFunLike.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonUnitalNonAssocSemiring.toMul.{u2} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (NonUnitalNonAssocSemiring.toMul.{u2} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (NonUnitalRingHomClass.toMulHomClass.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) (RingHomClass.toNonUnitalRingHomClass.{u2, u2, u2} (RingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (RingHom.instRingHomClassRingHom.{u2, u2} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u2} 𝕜 (CommSemiring.toSemiring.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (starRingEnd.{u2} 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u2} 𝕜 _inst_1)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x)
Case conversion may be inaccurate. Consider using '#align inner_self_conj inner_self_conjₓ'. -/
@[simp]
theorem inner_self_conj (x : E) : ⟪x, x⟫† = ⟪x, x⟫ := by
  rw [IsROrC.ext_iff] <;> exact ⟨by rw [conj_re], by rw [conj_im, inner_self_im, neg_zero]⟩
#align inner_self_conj inner_self_conj

/- warning: inner_sub_left -> inner_sub_left is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y) z) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x z) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y) z) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x z) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y z))
Case conversion may be inaccurate. Consider using '#align inner_sub_left inner_sub_leftₓ'. -/
theorem inner_sub_left (x y z : E) : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [sub_eq_add_neg, inner_add_left]
#align inner_sub_left inner_sub_left

/- warning: inner_sub_right -> inner_sub_right is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) y z)) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x z))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E) (z : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) y z)) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x z))
Case conversion may be inaccurate. Consider using '#align inner_sub_right inner_sub_rightₓ'. -/
theorem inner_sub_right (x y z : E) : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [sub_eq_add_neg, inner_add_right]
#align inner_sub_right inner_sub_right

/- warning: inner_mul_symm_re_eq_norm -> inner_mul_symm_re_eq_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_mul_symm_re_eq_norm inner_mul_symm_re_eq_normₓ'. -/
theorem inner_mul_symm_re_eq_norm (x y : E) : re (⟪x, y⟫ * ⟪y, x⟫) = ‖⟪x, y⟫ * ⟪y, x⟫‖ := by
  rw [← inner_conj_symm, mul_comm]; exact re_eq_norm_of_mul_conj (inner y x)
#align inner_mul_symm_re_eq_norm inner_mul_symm_re_eq_norm

/- warning: inner_add_add_self -> inner_add_add_self is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y y))
Case conversion may be inaccurate. Consider using '#align inner_add_add_self inner_add_add_selfₓ'. -/
/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self (x y : E) : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_add_left, inner_add_right] <;> ring
#align inner_add_add_self inner_add_add_self

/- warning: real_inner_add_add_self -> real_inner_add_add_self is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
Case conversion may be inaccurate. Consider using '#align real_inner_add_add_self real_inner_add_add_selfₓ'. -/
/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self (x y : F) : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
  by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm] <;> rfl
  simp only [inner_add_add_self, this, add_left_inj]
  ring
#align real_inner_add_add_self real_inner_add_add_self

/- warning: inner_sub_sub_self -> inner_sub_sub_self is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y)) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (HSub.hSub.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHSub.{u1} 𝕜 (SubNegMonoid.toHasSub.{u1} 𝕜 (AddGroup.toSubNegMonoid.{u1} 𝕜 (NormedAddGroup.toAddGroup.{u1} 𝕜 (NormedAddCommGroup.toNormedAddGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y y))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y)) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (HSub.hSub.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSub.{u2} 𝕜 (Ring.toSub.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y x)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y y))
Case conversion may be inaccurate. Consider using '#align inner_sub_sub_self inner_sub_sub_selfₓ'. -/
-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self (x y : E) : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [inner_sub_left, inner_sub_right] <;> ring
#align inner_sub_sub_self inner_sub_sub_self

/- warning: real_inner_sub_sub_self -> real_inner_sub_sub_self is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
Case conversion may be inaccurate. Consider using '#align real_inner_sub_sub_self real_inner_sub_sub_selfₓ'. -/
/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self (x y : F) : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ :=
  by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by rw [← inner_conj_symm] <;> rfl
  simp only [inner_sub_sub_self, this, add_left_inj]
  ring
#align real_inner_sub_sub_self real_inner_sub_sub_self

variable (𝕜)

include 𝕜

/- warning: ext_inner_left -> ext_inner_left is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (forall (v : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) v x) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) v y)) -> (Eq.{succ u2} E x y)
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (forall (v : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) v x) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) v y)) -> (Eq.{succ u1} E x y)
Case conversion may be inaccurate. Consider using '#align ext_inner_left ext_inner_leftₓ'. -/
theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_right, sub_eq_zero, h (x - y)]
#align ext_inner_left ext_inner_left

/- warning: ext_inner_right -> ext_inner_right is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (forall (v : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x v) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y v)) -> (Eq.{succ u2} E x y)
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (forall (v : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x v) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y v)) -> (Eq.{succ u1} E x y)
Case conversion may be inaccurate. Consider using '#align ext_inner_right ext_inner_rightₓ'. -/
theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  rw [← sub_eq_zero, ← @inner_self_eq_zero 𝕜, inner_sub_left, sub_eq_zero, h (x - y)]
#align ext_inner_right ext_inner_right

omit 𝕜

variable {𝕜}

/- warning: parallelogram_law -> parallelogram_law is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, Eq.{succ u1} 𝕜 (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y))) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (OfNat.ofNat.{u1} 𝕜 2 (OfNat.mk.{u1} 𝕜 2 (bit0.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))))) (HAdd.hAdd.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHAdd.{u1} 𝕜 (Distrib.toHasAdd.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) y y)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, Eq.{succ u2} 𝕜 (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y))) (HMul.hMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHMul.{u2} 𝕜 (NonUnitalNonAssocRing.toMul.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u2} 𝕜 2 (instOfNat.{u2} 𝕜 2 (Semiring.toNatCast.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHAdd.{u2} 𝕜 (Distrib.toAdd.{u2} 𝕜 (NonUnitalNonAssocSemiring.toDistrib.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x x) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) y y)))
Case conversion may be inaccurate. Consider using '#align parallelogram_law parallelogram_lawₓ'. -/
/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp [inner_add_add_self, inner_sub_sub_self, two_mul, sub_eq_add_neg, add_comm, add_left_comm]
#align parallelogram_law parallelogram_law

/- warning: inner_mul_inner_self_le -> inner_mul_inner_self_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_mul_inner_self_le inner_mul_inner_self_leₓ'. -/
/-- **Cauchy–Schwarz inequality**. -/
theorem inner_mul_inner_self_le (x y : E) : ‖⟪x, y⟫‖ * ‖⟪y, x⟫‖ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ :=
  letI c : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
  InnerProductSpace.Core.inner_mul_inner_self_le x y
#align inner_mul_inner_self_le inner_mul_inner_self_le

/- warning: real_inner_mul_inner_self_le -> real_inner_mul_inner_self_le is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.hasLe (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.instLEReal (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) y y))
Case conversion may be inaccurate. Consider using '#align real_inner_mul_inner_self_le real_inner_mul_inner_self_leₓ'. -/
/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ :=
  calc
    ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ‖⟪x, y⟫_ℝ‖ * ‖⟪y, x⟫_ℝ‖ := by rw [real_inner_comm y, ← norm_mul];
      exact le_abs_self _
    _ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ := @inner_mul_inner_self_le ℝ _ _ _ _ x y
    
#align real_inner_mul_inner_self_le real_inner_mul_inner_self_le

/- warning: linear_independent_of_ne_zero_of_inner_eq_zero -> linearIndependent_of_ne_zero_of_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (forall (i : ι), Ne.{succ u2} E (v i) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) -> (forall (i : ι) (j : ι), (Ne.{succ u3} ι i j) -> (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) (v j)) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))))))) -> (LinearIndependent.{u3, u1, u2} ι 𝕜 E v (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (forall (i : ι), Ne.{succ u2} E (v i) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) -> (forall (i : ι) (j : ι), (Ne.{succ u3} ι i j) -> (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) (v j)) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) -> (LinearIndependent.{u3, u1, u2} ι 𝕜 E v (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align linear_independent_of_ne_zero_of_inner_eq_zero linearIndependent_of_ne_zero_of_inner_eq_zeroₓ'. -/
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
      rw [inner_smul_right, ho i j hji.symm, MulZeroClass.mul_zero]
    · exact fun h => False.elim (h hi)
  simpa [hg, hz] using h'
#align linear_independent_of_ne_zero_of_inner_eq_zero linearIndependent_of_ne_zero_of_inner_eq_zero

end BasicProperties

section OrthonormalSets

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

include 𝕜

#print Orthonormal /-
/-- An orthonormal set of vectors in an `inner_product_space` -/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ‖v i‖ = 1) ∧ ∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0
#align orthonormal Orthonormal
-/

omit 𝕜

variable {𝕜}

include dec_ι

/- warning: orthonormal_iff_ite -> orthonormal_iff_ite is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [dec_ι : DecidableEq.{succ u3} ι] {v : ι -> E}, Iff (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) (forall (i : ι) (j : ι), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) (v j)) (ite.{succ u1} 𝕜 (Eq.{succ u3} ι i j) (dec_ι i j) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} [dec_ι : DecidableEq.{succ u1} ι] {v : ι -> E}, Iff (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) (forall (i : ι) (j : ι), Eq.{succ u3} 𝕜 (Inner.inner.{u3, u2} 𝕜 E (InnerProductSpace.toInner.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) (v j)) (ite.{succ u3} 𝕜 (Eq.{succ u1} ι i j) (dec_ι i j) (OfNat.ofNat.{u3} 𝕜 1 (One.toOfNat1.{u3} 𝕜 (Semiring.toOne.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u3} 𝕜 0 (Zero.toOfNat0.{u3} 𝕜 (CommMonoidWithZero.toZero.{u3} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u3} 𝕜 (Semifield.toCommGroupWithZero.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))))))))
Case conversion may be inaccurate. Consider using '#align orthonormal_iff_ite orthonormal_iff_iteₓ'. -/
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
      have h' : ‖v i‖ ^ 2 = 1 ^ 2 := by simp [@norm_sq_eq_inner 𝕜, h i i]
      have h₁ : 0 ≤ ‖v i‖ := norm_nonneg _
      have h₂ : (0 : ℝ) ≤ 1 := zero_le_one
      rwa [sq_eq_sq h₁ h₂] at h'
    · intro i j hij
      simpa [hij] using h i j
#align orthonormal_iff_ite orthonormal_iff_ite

omit dec_ι

include dec_E

/- warning: orthonormal_subtype_iff_ite -> orthonormal_subtype_iff_ite is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [dec_E : DecidableEq.{succ u2} E] {s : Set.{u2} E}, Iff (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s))))))) (forall (v : E), (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) v s) -> (forall (w : E), (Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) w s) -> (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) v w) (ite.{succ u1} 𝕜 (Eq.{succ u2} E v w) (dec_E v w) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [dec_E : DecidableEq.{succ u2} E] {s : Set.{u2} E}, Iff (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s)) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x s))) (forall (v : E), (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) v s) -> (forall (w : E), (Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) w s) -> (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) v w) (ite.{succ u1} 𝕜 (Eq.{succ u2} E v w) (dec_E v w) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (Semiring.toOne.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (OfNat.ofNat.{u1} 𝕜 0 (Zero.toOfNat0.{u1} 𝕜 (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))
Case conversion may be inaccurate. Consider using '#align orthonormal_subtype_iff_ite orthonormal_subtype_iff_iteₓ'. -/
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

/- warning: orthonormal.inner_right_finsupp -> Orthonormal.inner_right_finsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_right_finsupp Orthonormal.inner_right_finsuppₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = l i := by
  classical simp [Finsupp.total_apply, Finsupp.inner_sum, orthonormal_iff_ite.mp hv]
#align orthonormal.inner_right_finsupp Orthonormal.inner_right_finsupp

/- warning: orthonormal.inner_right_sum -> Orthonormal.inner_right_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_right_sum Orthonormal.inner_right_sumₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪v i, ∑ i in s, l i • v i⟫ = l i := by
  classical simp [inner_sum, inner_smul_right, orthonormal_iff_ite.mp hv, hi]
#align orthonormal.inner_right_sum Orthonormal.inner_right_sum

/- warning: orthonormal.inner_right_fintype -> Orthonormal.inner_right_fintype is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_right_fintype Orthonormal.inner_right_fintypeₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)
#align orthonormal.inner_right_fintype Orthonormal.inner_right_fintype

/- warning: orthonormal.inner_left_finsupp -> Orthonormal.inner_left_finsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_left_finsupp Orthonormal.inner_left_finsuppₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) := by rw [← inner_conj_symm, hv.inner_right_finsupp]
#align orthonormal.inner_left_finsupp Orthonormal.inner_left_finsupp

/- warning: orthonormal.inner_left_sum -> Orthonormal.inner_left_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_left_sum Orthonormal.inner_left_sumₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι}
    {i : ι} (hi : i ∈ s) : ⟪∑ i in s, l i • v i, v i⟫ = conj (l i) := by
  classical simp only [sum_inner, inner_smul_left, orthonormal_iff_ite.mp hv, hi, mul_boole,
      Finset.sum_ite_eq', if_true]
#align orthonormal.inner_left_sum Orthonormal.inner_left_sum

/- warning: orthonormal.inner_left_fintype -> Orthonormal.inner_left_fintype is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_left_fintype Orthonormal.inner_left_fintypeₓ'. -/
/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜)
    (i : ι) : ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)
#align orthonormal.inner_left_fintype Orthonormal.inner_left_fintype

/- warning: orthonormal.inner_finsupp_eq_sum_left -> Orthonormal.inner_finsupp_eq_sum_left is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_finsupp_eq_sum_left Orthonormal.inner_finsupp_eq_sum_leftₓ'. -/
/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₁.Sum fun i y => conj y * l₂ i := by
  simp only [l₁.total_apply _, Finsupp.sum_inner, hv.inner_right_finsupp, smul_eq_mul]
#align orthonormal.inner_finsupp_eq_sum_left Orthonormal.inner_finsupp_eq_sum_left

/- warning: orthonormal.inner_finsupp_eq_sum_right -> Orthonormal.inner_finsupp_eq_sum_right is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_finsupp_eq_sum_right Orthonormal.inner_finsupp_eq_sum_rightₓ'. -/
/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₂.Sum fun i y => conj (l₁ i) * y := by
  simp only [l₂.total_apply _, Finsupp.inner_sum, hv.inner_left_finsupp, mul_comm, smul_eq_mul]
#align orthonormal.inner_finsupp_eq_sum_right Orthonormal.inner_finsupp_eq_sum_right

/- warning: orthonormal.inner_sum -> Orthonormal.inner_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_sum Orthonormal.inner_sumₓ'. -/
/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
theorem Orthonormal.inner_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι → 𝕜) (s : Finset ι) :
    ⟪∑ i in s, l₁ i • v i, ∑ i in s, l₂ i • v i⟫ = ∑ i in s, conj (l₁ i) * l₂ i :=
  by
  simp_rw [sum_inner, inner_smul_left]
  refine' Finset.sum_congr rfl fun i hi => _
  rw [hv.inner_right_sum l₂ hi]
#align orthonormal.inner_sum Orthonormal.inner_sum

/- warning: orthonormal.inner_left_right_finset -> Orthonormal.inner_left_right_finset is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {s : Finset.{u3} ι} {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (forall {a : ι -> ι -> 𝕜}, Eq.{succ u1} 𝕜 (Finset.sum.{u1, u3} 𝕜 ι (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) s (fun (i : ι) => Finset.sum.{u1, u3} 𝕜 ι (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) s (fun (j : ι) => SMul.smul.{u1, u1} 𝕜 𝕜 (Mul.toSMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (a i j) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v j) (v i))))) (Finset.sum.{u1, u3} 𝕜 ι (AddCommGroup.toAddCommMonoid.{u1} 𝕜 (NormedAddCommGroup.toAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) s (fun (k : ι) => a k k)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [s : DecidableEq.{succ u3} ι] {v : Finset.{u3} ι} {hv : ι -> E}, (Orthonormal.{u2, u1, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv) -> (forall {a : ι -> ι -> 𝕜}, Eq.{succ u2} 𝕜 (Finset.sum.{u2, u3} 𝕜 ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) v (fun (i : ι) => Finset.sum.{u2, u3} 𝕜 ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) v (fun (j : ι) => HSMul.hSMul.{u2, u2, u2} 𝕜 𝕜 𝕜 (instHSMul.{u2, u2} 𝕜 𝕜 (Algebra.toSMul.{u2, u2} 𝕜 𝕜 (Semifield.toCommSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (NormedAlgebra.toAlgebra.{u2, u2} 𝕜 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))) (NormedAlgebra.id.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (a i j) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (hv j) (hv i))))) (Finset.sum.{u2, u3} 𝕜 ι (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u2} 𝕜 (Ring.toNonAssocRing.{u2} 𝕜 (NormedRing.toRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) v (fun (k : ι) => a k k)))
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_left_right_finset Orthonormal.inner_left_right_finsetₓ'. -/
/--
The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal 𝕜 v)
    {a : ι → ι → 𝕜} : (∑ i in s, ∑ j in s, a i j • ⟪v j, v i⟫) = ∑ k in s, a k k := by
  classical simp [orthonormal_iff_ite.mp hv, Finset.sum_ite_of_true]
#align orthonormal.inner_left_right_finset Orthonormal.inner_left_right_finset

/- warning: orthonormal.linear_independent -> Orthonormal.linearIndependent is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (LinearIndependent.{u3, u1, u2} ι 𝕜 E v (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} [v : DecidableEq.{succ u1} ι] {hv : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv) -> (LinearIndependent.{u1, u3, u2} ι 𝕜 E hv (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u3, u2} 𝕜 E (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align orthonormal.linear_independent Orthonormal.linearIndependentₓ'. -/
/-- An orthonormal set is linearly independent. -/
theorem Orthonormal.linearIndependent {v : ι → E} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v :=
  by
  rw [linearIndependent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by rw [hl]
  simpa only [hv.inner_right_finsupp, inner_zero_right] using key
#align orthonormal.linear_independent Orthonormal.linearIndependent

/- warning: orthonormal.comp -> Orthonormal.comp is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {ι' : Type.{u4}} {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (forall (f : ι' -> ι), (Function.Injective.{succ u4, succ u3} ι' ι f) -> (Orthonormal.{u1, u2, u4} 𝕜 E _inst_1 _inst_2 _inst_3 ι' (Function.comp.{succ u4, succ u3, succ u2} ι' ι E v f)))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} [ι' : DecidableEq.{succ u1} ι] {v : Type.{u4}} {hv : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv) -> (forall (hf : v -> ι), (Function.Injective.{succ u4, succ u1} v ι hf) -> (Orthonormal.{u3, u2, u4} 𝕜 E _inst_1 _inst_2 _inst_3 v (Function.comp.{succ u4, succ u1, succ u2} v ι E hv hf)))
Case conversion may be inaccurate. Consider using '#align orthonormal.comp Orthonormal.compₓ'. -/
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

/- warning: orthonormal_subtype_range -> orthonormal_subtype_range is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (Function.Injective.{succ u3, succ u2} ι E v) -> (Iff (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (Set.range.{u2, succ u3} E ι v)))))))) (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [ι : DecidableEq.{succ u2} E] {v : Type.{u3}} [hv : DecidableEq.{succ u3} v] {v_1 : v -> E}, (Function.Injective.{succ u3, succ u2} v E v_1) -> (Iff (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u3} E v v_1))) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u3} E v v_1)))) (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 v v_1))
Case conversion may be inaccurate. Consider using '#align orthonormal_subtype_range orthonormal_subtype_rangeₓ'. -/
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

/- warning: orthonormal.to_subtype_range -> Orthonormal.toSubtypeRange is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.range.{u2, succ u3} E ι v)) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (Set.range.{u2, succ u3} E ι v))))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] [ι : DecidableEq.{succ u2} E] {v : Type.{u1}} [hv : DecidableEq.{succ u1} v] {v_1 : v -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 v v_1) -> (Orthonormal.{u3, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u1} E v v_1))) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.range.{u2, succ u1} E v v_1))))
Case conversion may be inaccurate. Consider using '#align orthonormal.to_subtype_range Orthonormal.toSubtypeRangeₓ'. -/
/-- If `v : ι → E` is an orthonormal family, then `coe : (range v) → E` is an orthonormal
family. -/
theorem Orthonormal.toSubtypeRange {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Orthonormal 𝕜 (coe : Set.range v → E) :=
  (orthonormal_subtype_range hv.LinearIndependent.Injective).2 hv
#align orthonormal.to_subtype_range Orthonormal.toSubtypeRange

/- warning: orthonormal.inner_finsupp_eq_zero -> Orthonormal.inner_finsupp_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_finsupp_eq_zero Orthonormal.inner_finsupp_eq_zeroₓ'. -/
/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι}
    (hi : i ∉ s) {l : ι →₀ 𝕜} (hl : l ∈ Finsupp.supported 𝕜 𝕜 s) :
    ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = 0 :=
  by
  rw [Finsupp.mem_supported'] at hl
  simp only [hv.inner_left_finsupp, hl i hi, map_zero]
#align orthonormal.inner_finsupp_eq_zero Orthonormal.inner_finsupp_eq_zero

/- warning: orthonormal.orthonormal_of_forall_eq_or_eq_neg -> Orthonormal.orthonormal_of_forall_eq_or_eq_neg is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E} {w : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (forall (i : ι), Or (Eq.{succ u2} E (w i) (v i)) (Eq.{succ u2} E (w i) (Neg.neg.{u2} E (SubNegMonoid.toHasNeg.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))) (v i)))) -> (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι w)
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} [v : DecidableEq.{succ u1} ι] {w : ι -> E} {hv : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι w) -> (forall (i : ι), Or (Eq.{succ u2} E (hv i) (w i)) (Eq.{succ u2} E (hv i) (Neg.neg.{u2} E (NegZeroClass.toNeg.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (w i)))) -> (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv)
Case conversion may be inaccurate. Consider using '#align orthonormal.orthonormal_of_forall_eq_or_eq_neg Orthonormal.orthonormal_of_forall_eq_or_eq_negₓ'. -/
/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι → E} (hv : Orthonormal 𝕜 v)
    (hw : ∀ i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w := by
  classical
    rw [orthonormal_iff_ite] at *
    intro i j
    cases' hw i with hi hi <;> cases' hw j with hj hj <;> split_ifs with h <;>
      simpa only [hi, hj, h, inner_neg_right, inner_neg_left, neg_neg, eq_self_iff_true,
        neg_eq_zero] using hv i j
#align orthonormal.orthonormal_of_forall_eq_or_eq_neg Orthonormal.orthonormal_of_forall_eq_or_eq_neg

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/
variable (𝕜 E)

/- warning: orthonormal_empty -> orthonormal_empty is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) (E : Type.{u2}) [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2], Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (EmptyCollection.emptyCollection.{u2} (Set.{u2} E) (Set.hasEmptyc.{u2} E))))))) x)
but is expected to have type
  forall (𝕜 : Type.{u2}) (E : Type.{u1}) [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] [dec_E : DecidableEq.{succ u1} E], Orthonormal.{u2, u1, u1} 𝕜 E _inst_1 _inst_2 _inst_3 (Set.Elem.{u1} E (EmptyCollection.emptyCollection.{u1} (Set.{u1} E) (Set.instEmptyCollectionSet.{u1} E))) (fun (x : Set.Elem.{u1} E (EmptyCollection.emptyCollection.{u1} (Set.{u1} E) (Set.instEmptyCollectionSet.{u1} E))) => Subtype.val.{succ u1} E (fun (x : E) => Membership.mem.{u1, u1} E (Set.{u1} E) (Set.instMembershipSet.{u1} E) x (EmptyCollection.emptyCollection.{u1} (Set.{u1} E) (Set.instEmptyCollectionSet.{u1} E))) x)
Case conversion may be inaccurate. Consider using '#align orthonormal_empty orthonormal_emptyₓ'. -/
theorem orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) → E) := by
  classical simp [orthonormal_subtype_iff_ite]
#align orthonormal_empty orthonormal_empty

variable {𝕜 E}

/- warning: orthonormal_Union_of_directed -> orthonormal_iUnion_of_directed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {η : Type.{u3}} {s : η -> (Set.{u2} E)}, (Directed.{u2, succ u3} (Set.{u2} E) η (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E)) s) -> (forall (i : η), Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (s i)) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (s i)))))) x)) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (Set.iUnion.{u2, succ u3} E η (fun (i : η) => s i))))))) x))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [η : DecidableEq.{succ u2} E] {s : Type.{u3}} {hs : s -> (Set.{u2} E)}, (Directed.{u2, succ u3} (Set.{u2} E) s (fun (x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14494 : Set.{u2} E) (x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14496 : Set.{u2} E) => HasSubset.Subset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14494 x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14496) hs) -> (forall (i : s), Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Set.Elem.{u2} E (hs i)) (fun (x : Set.Elem.{u2} E (hs i)) => Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (hs i)) x)) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Set.Elem.{u2} E (Set.iUnion.{u2, succ u3} E s (fun (i : s) => hs i))) (fun (x : Set.Elem.{u2} E (Set.iUnion.{u2, succ u3} E s (fun (i : s) => hs i))) => Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.iUnion.{u2, succ u3} E s (fun (i : s) => hs i))) x))
Case conversion may be inaccurate. Consider using '#align orthonormal_Union_of_directed orthonormal_iUnion_of_directedₓ'. -/
theorem orthonormal_iUnion_of_directed {η : Type _} {s : η → Set E} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, Orthonormal 𝕜 (fun x => x : s i → E)) : Orthonormal 𝕜 (fun x => x : (⋃ i, s i) → E) :=
  by
  classical
    rw [orthonormal_subtype_iff_ite]
    rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
    obtain ⟨k, hik, hjk⟩ := hs i j
    have h_orth : Orthonormal 𝕜 (fun x => x : s k → E) := h k
    rw [orthonormal_subtype_iff_ite] at h_orth
    exact h_orth x (hik hxi) y (hjk hyj)
#align orthonormal_Union_of_directed orthonormal_iUnion_of_directed

/- warning: orthonormal_sUnion_of_directed -> orthonormal_sUnion_of_directed is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {s : Set.{u2} (Set.{u2} E)}, (DirectedOn.{u2} (Set.{u2} E) (HasSubset.Subset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E)) s) -> (forall (a : Set.{u2} E), (Membership.Mem.{u2, u2} (Set.{u2} E) (Set.{u2} (Set.{u2} E)) (Set.hasMem.{u2} (Set.{u2} E)) a s) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) a) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x a))))) x))) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) (fun (x : coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) => (fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) (Set.sUnion.{u2} E s)) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x (Set.sUnion.{u2} E s)))))) x))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [s : DecidableEq.{succ u2} E] {hs : Set.{u2} (Set.{u2} E)}, (DirectedOn.{u2} (Set.{u2} E) (fun (x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14712 : Set.{u2} E) (x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14714 : Set.{u2} E) => HasSubset.Subset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14712 x._@.Mathlib.Analysis.InnerProductSpace.Basic._hyg.14714) hs) -> (forall (a : Set.{u2} E), (Membership.mem.{u2, u2} (Set.{u2} E) (Set.{u2} (Set.{u2} E)) (Set.instMembershipSet.{u2} (Set.{u2} E)) a hs) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Set.Elem.{u2} E a) (fun (x : Set.Elem.{u2} E a) => Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x a) x))) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Set.Elem.{u2} E (Set.sUnion.{u2} E hs)) (fun (x : Set.Elem.{u2} E (Set.sUnion.{u2} E hs)) => Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x (Set.sUnion.{u2} E hs)) x))
Case conversion may be inaccurate. Consider using '#align orthonormal_sUnion_of_directed orthonormal_sUnion_of_directedₓ'. -/
theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, Orthonormal 𝕜 (fun x => x : (a : Set E) → E)) :
    Orthonormal 𝕜 (fun x => x : ⋃₀ s → E) := by
  rw [Set.sUnion_eq_iUnion] <;>
    exact orthonormal_iUnion_of_directed hs.directed_coe (by simpa using h)
#align orthonormal_sUnion_of_directed orthonormal_sUnion_of_directed

/- warning: exists_maximal_orthonormal -> exists_maximal_orthonormal is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {s : Set.{u2} E}, (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) s) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x s))))))) -> (Exists.{succ u2} (Set.{u2} E) (fun (w : Set.{u2} E) => Exists.{0} (Superset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) w s) (fun (H : Superset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) w s) => And (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) w) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) w) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) w) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) w) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) w) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x w))))))) (forall (u : Set.{u2} E), (Superset.{u2} (Set.{u2} E) (Set.hasSubset.{u2} E) u w) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) u) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) u) E (HasLiftT.mk.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) u) E (CoeTCₓ.coe.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) u) E (coeBase.{succ u2, succ u2} (coeSort.{succ u2, succ (succ u2)} (Set.{u2} E) Type.{u2} (Set.hasCoeToSort.{u2} E) u) E (coeSubtype.{succ u2} E (fun (x : E) => Membership.Mem.{u2, u2} E (Set.{u2} E) (Set.hasMem.{u2} E) x u))))))) -> (Eq.{succ u2} (Set.{u2} E) u w)))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] [s : DecidableEq.{succ u2} E] {hs : Set.{u2} E}, (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x hs)) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x hs))) -> (Exists.{succ u2} (Set.{u2} E) (fun (w : Set.{u2} E) => Exists.{0} (Superset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) w hs) (fun (_hw : Superset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) w hs) => And (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x w)) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x w))) (forall (u : Set.{u2} E), (Superset.{u2} (Set.{u2} E) (Set.instHasSubsetSet.{u2} E) u w) -> (Orthonormal.{u1, u2, u2} 𝕜 E _inst_1 _inst_2 _inst_3 (Subtype.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x u)) (Subtype.val.{succ u2} E (fun (x : E) => Membership.mem.{u2, u2} E (Set.{u2} E) (Set.instMembershipSet.{u2} E) x u))) -> (Eq.{succ u2} (Set.{u2} E) u w)))))
Case conversion may be inaccurate. Consider using '#align exists_maximal_orthonormal exists_maximal_orthonormalₓ'. -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (w «expr ⊇ » s) -/
/- ./././Mathport/Syntax/Translate/Basic.lean:635:2: warning: expanding binder collection (u «expr ⊇ » w) -/
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
    · exact orthonormal_sUnion_of_directed cc.directed_on fun x xc => hc xc
    · exact fun _ => Set.subset_sUnion_of_mem
#align exists_maximal_orthonormal exists_maximal_orthonormal

/- warning: orthonormal.ne_zero -> Orthonormal.ne_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (forall (i : ι), Ne.{succ u2} E (v i) (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} {v : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (forall (i : ι), Ne.{succ u2} E (v i) (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))))))
Case conversion may be inaccurate. Consider using '#align orthonormal.ne_zero Orthonormal.ne_zeroₓ'. -/
theorem Orthonormal.ne_zero {v : ι → E} (hv : Orthonormal 𝕜 v) (i : ι) : v i ≠ 0 :=
  by
  have : ‖v i‖ ≠ 0 := by
    rw [hv.1 i]
    norm_num
  simpa using this
#align orthonormal.ne_zero Orthonormal.ne_zero

open FiniteDimensional

/- warning: basis_of_orthonormal_of_card_eq_finrank -> basisOfOrthonormalOfCardEqFinrank is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [_inst_6 : Fintype.{u3} ι] [_inst_7 : Nonempty.{succ u3} ι] {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (Eq.{1} Nat (Fintype.card.{u3} ι _inst_6) (FiniteDimensional.finrank.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) -> (Basis.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [_inst_6 : DecidableEq.{succ u3} ι] [_inst_7 : Fintype.{u3} ι] [v : Nonempty.{succ u3} ι] {hv : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv) -> (Eq.{1} Nat (Fintype.card.{u3} ι _inst_7) (FiniteDimensional.finrank.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) -> (Basis.{u3, u1, u2} ι 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))
Case conversion may be inaccurate. Consider using '#align basis_of_orthonormal_of_card_eq_finrank basisOfOrthonormalOfCardEqFinrankₓ'. -/
/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.LinearIndependent card_eq
#align basis_of_orthonormal_of_card_eq_finrank basisOfOrthonormalOfCardEqFinrank

/- warning: coe_basis_of_orthonormal_of_card_eq_finrank -> coe_basisOfOrthonormalOfCardEqFinrank is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [_inst_6 : Fintype.{u3} ι] [_inst_7 : Nonempty.{succ u3} ι] {v : ι -> E} (hv : Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) (card_eq : Eq.{1} Nat (Fintype.card.{u3} ι _inst_6) (FiniteDimensional.finrank.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))), Eq.{max (succ u3) (succ u2)} ((fun (_x : Basis.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) => ι -> E) (basisOfOrthonormalOfCardEqFinrank.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι _inst_6 _inst_7 v hv card_eq)) (coeFn.{max (succ u3) (succ u1) (succ u2), max (succ u3) (succ u2)} (Basis.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (fun (_x : Basis.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) => ι -> E) (FunLike.hasCoeToFun.{max (succ u3) (succ u1) (succ u2), succ u3, succ u2} (Basis.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) ι (fun (_x : ι) => E) (Basis.funLike.{u3, u1, u2} ι 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))) (basisOfOrthonormalOfCardEqFinrank.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι _inst_6 _inst_7 v hv card_eq)) v
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} [_inst_6 : DecidableEq.{succ u3} ι] [_inst_7 : Fintype.{u3} ι] [v : Nonempty.{succ u3} ι] {hv : ι -> E} (card_eq : Orthonormal.{u2, u1, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι hv) (card_eq_1 : Eq.{1} Nat (Fintype.card.{u3} ι _inst_7) (FiniteDimensional.finrank.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)))), Eq.{max (succ u1) (succ u3)} (forall (a : ι), (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => E) a) (FunLike.coe.{max (max (succ u2) (succ u1)) (succ u3), succ u3, succ u1} (Basis.{u3, u2, u1} ι 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))) ι (fun (a : ι) => (fun (x._@.Mathlib.LinearAlgebra.Basis._hyg.548 : ι) => E) a) (Basis.funLike.{u3, u2, u1} ι 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))) (basisOfOrthonormalOfCardEqFinrank.{u2, u1, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι (fun (a : ι) (b : ι) => _inst_6 a b) _inst_7 v hv card_eq card_eq_1)) hv
Case conversion may be inaccurate. Consider using '#align coe_basis_of_orthonormal_of_card_eq_finrank coe_basisOfOrthonormalOfCardEqFinrankₓ'. -/
@[simp]
theorem coe_basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E}
    (hv : Orthonormal 𝕜 v) (card_eq : Fintype.card ι = finrank 𝕜 E) :
    (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _
#align coe_basis_of_orthonormal_of_card_eq_finrank coe_basisOfOrthonormalOfCardEqFinrank

end OrthonormalSets

section Norm

/- warning: norm_eq_sqrt_inner -> norm_eq_sqrt_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_eq_sqrt_inner norm_eq_sqrt_innerₓ'. -/
theorem norm_eq_sqrt_inner (x : E) : ‖x‖ = sqrt (re ⟪x, x⟫) :=
  calc
    ‖x‖ = sqrt (‖x‖ ^ 2) := (sqrt_sq (norm_nonneg _)).symm
    _ = sqrt (re ⟪x, x⟫) := congr_arg _ (norm_sq_eq_inner _)
    
#align norm_eq_sqrt_inner norm_eq_sqrt_inner

#print norm_eq_sqrt_real_inner /-
theorem norm_eq_sqrt_real_inner (x : F) : ‖x‖ = sqrt ⟪x, x⟫_ℝ :=
  @norm_eq_sqrt_inner ℝ _ _ _ _ x
#align norm_eq_sqrt_real_inner norm_eq_sqrt_real_inner
-/

/- warning: inner_self_eq_norm_mul_norm -> inner_self_eq_norm_mul_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_eq_norm_mul_norm inner_self_eq_norm_mul_normₓ'. -/
theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ‖x‖ * ‖x‖ := by
  rw [@norm_eq_sqrt_inner 𝕜, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫),
    sqrt_mul_self inner_self_nonneg]
#align inner_self_eq_norm_mul_norm inner_self_eq_norm_mul_norm

/- warning: inner_self_eq_norm_sq -> inner_self_eq_norm_sq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_self_eq_norm_sq inner_self_eq_norm_sqₓ'. -/
theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ‖x‖ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]
#align inner_self_eq_norm_sq inner_self_eq_norm_sq

/- warning: real_inner_self_eq_norm_mul_norm -> real_inner_self_eq_norm_mul_norm is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x))
Case conversion may be inaccurate. Consider using '#align real_inner_self_eq_norm_mul_norm real_inner_self_eq_norm_mul_normₓ'. -/
theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ‖x‖ * ‖x‖ := by
  have h := @inner_self_eq_norm_mul_norm ℝ F _ _ _ x; simpa using h
#align real_inner_self_eq_norm_mul_norm real_inner_self_eq_norm_mul_norm

/- warning: real_inner_self_eq_norm_sq -> real_inner_self_eq_norm_sq is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x x) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))
Case conversion may be inaccurate. Consider using '#align real_inner_self_eq_norm_sq real_inner_self_eq_norm_sqₓ'. -/
theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ‖x‖ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]
#align real_inner_self_eq_norm_sq real_inner_self_eq_norm_sq

variable (𝕜)

/- warning: norm_add_sq -> norm_add_sq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_add_sq norm_add_sqₓ'. -/
/-- Expand the square -/
theorem norm_add_sq (x y : E) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 :=
  by
  repeat' rw [sq, ← @inner_self_eq_norm_mul_norm 𝕜]
  rw [inner_add_add_self, two_mul]
  simp only [add_assoc, add_left_inj, add_right_inj, AddMonoidHom.map_add]
  rw [← inner_conj_symm, conj_re]
#align norm_add_sq norm_add_sq

/- warning: norm_add_pow_two -> norm_add_pow_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_add_pow_two norm_add_pow_twoₓ'. -/
alias norm_add_sq ← norm_add_pow_two
#align norm_add_pow_two norm_add_pow_two

/- warning: norm_add_sq_real -> norm_add_sq_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align norm_add_sq_real norm_add_sq_realₓ'. -/
/-- Expand the square -/
theorem norm_add_sq_real (x y : F) : ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 := by
  have h := @norm_add_sq ℝ _ _ _ _ x y; simpa using h
#align norm_add_sq_real norm_add_sq_real

/- warning: norm_add_pow_two_real -> norm_add_pow_two_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align norm_add_pow_two_real norm_add_pow_two_realₓ'. -/
alias norm_add_sq_real ← norm_add_pow_two_real
#align norm_add_pow_two_real norm_add_pow_two_real

/- warning: norm_add_mul_self -> norm_add_mul_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_add_mul_self norm_add_mul_selfₓ'. -/
/-- Expand the square -/
theorem norm_add_mul_self (x y : E) : ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ :=
  by repeat' rw [← sq]; exact norm_add_sq _ _
#align norm_add_mul_self norm_add_mul_self

/- warning: norm_add_mul_self_real -> norm_add_mul_self_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))
Case conversion may be inaccurate. Consider using '#align norm_add_mul_self_real norm_add_mul_self_realₓ'. -/
/-- Expand the square -/
theorem norm_add_mul_self_real (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_add_mul_self ℝ _ _ _ _ x y; simpa using h
#align norm_add_mul_self_real norm_add_mul_self_real

/- warning: norm_sub_sq -> norm_sub_sq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_sub_sq norm_sub_sqₓ'. -/
/-- Expand the square -/
theorem norm_sub_sq (x y : E) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * re ⟪x, y⟫ + ‖y‖ ^ 2 := by
  rw [sub_eq_add_neg, @norm_add_sq 𝕜 _ _ _ _ x (-y), norm_neg, inner_neg_right, map_neg, mul_neg,
    sub_eq_add_neg]
#align norm_sub_sq norm_sub_sq

/- warning: norm_sub_pow_two -> norm_sub_pow_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_sub_pow_two norm_sub_pow_twoₓ'. -/
alias norm_sub_sq ← norm_sub_pow_two
#align norm_sub_pow_two norm_sub_pow_two

/- warning: norm_sub_sq_real -> norm_sub_sq_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align norm_sub_sq_real norm_sub_sq_realₓ'. -/
/-- Expand the square -/
theorem norm_sub_sq_real (x y : F) : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * ⟪x, y⟫_ℝ + ‖y‖ ^ 2 :=
  @norm_sub_sq ℝ _ _ _ _ _ _
#align norm_sub_sq_real norm_sub_sq_real

/- warning: norm_sub_pow_two_real -> norm_sub_pow_two_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align norm_sub_pow_two_real norm_sub_pow_two_realₓ'. -/
alias norm_sub_sq_real ← norm_sub_pow_two_real
#align norm_sub_pow_two_real norm_sub_pow_two_real

/- warning: norm_sub_mul_self -> norm_sub_mul_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_sub_mul_self norm_sub_mul_selfₓ'. -/
/-- Expand the square -/
theorem norm_sub_mul_self (x y : E) : ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * re ⟪x, y⟫ + ‖y‖ * ‖y‖ :=
  by repeat' rw [← sq]; exact norm_sub_sq _ _
#align norm_sub_mul_self norm_sub_mul_self

/- warning: norm_sub_mul_self_real -> norm_sub_mul_self_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))
Case conversion may be inaccurate. Consider using '#align norm_sub_mul_self_real norm_sub_mul_self_realₓ'. -/
/-- Expand the square -/
theorem norm_sub_mul_self_real (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ - 2 * ⟪x, y⟫_ℝ + ‖y‖ * ‖y‖ := by
  have h := @norm_sub_mul_self ℝ _ _ _ _ x y; simpa using h
#align norm_sub_mul_self_real norm_sub_mul_self_real

/- warning: norm_inner_le_norm -> norm_inner_le_norm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), LE.le.{0} Real Real.hasLe (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y))
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), LE.le.{0} Real Real.instLEReal (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) y))
Case conversion may be inaccurate. Consider using '#align norm_inner_le_norm norm_inner_le_normₓ'. -/
/-- Cauchy–Schwarz inequality with norm -/
theorem norm_inner_le_norm (x y : E) : ‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖ :=
  by
  rw [norm_eq_sqrt_inner x, norm_eq_sqrt_inner y]
  letI : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
  exact InnerProductSpace.Core.norm_inner_le_norm x y
#align norm_inner_le_norm norm_inner_le_norm

/- warning: nnnorm_inner_le_nnnorm -> nnnorm_inner_le_nnnorm is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), LE.le.{0} NNReal (Preorder.toHasLe.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (OrderedCancelAddCommMonoid.toPartialOrder.{0} NNReal (StrictOrderedSemiring.toOrderedCancelAddCommMonoid.{0} NNReal NNReal.strictOrderedSemiring)))) (NNNorm.nnnorm.{u1} 𝕜 (SeminormedAddGroup.toNNNorm.{u1} 𝕜 (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u1} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) x) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) y))
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), LE.le.{0} NNReal (Preorder.toLE.{0} NNReal (PartialOrder.toPreorder.{0} NNReal (StrictOrderedSemiring.toPartialOrder.{0} NNReal instNNRealStrictOrderedSemiring))) (NNNorm.nnnorm.{u2} 𝕜 (SeminormedAddGroup.toNNNorm.{u2} 𝕜 (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} 𝕜 (NonUnitalSeminormedRing.toSeminormedAddCommGroup.{u2} 𝕜 (NonUnitalNormedRing.toNonUnitalSeminormedRing.{u2} 𝕜 (NormedRing.toNonUnitalNormedRing.{u2} 𝕜 (NormedCommRing.toNormedRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) x) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) y))
Case conversion may be inaccurate. Consider using '#align nnnorm_inner_le_nnnorm nnnorm_inner_le_nnnormₓ'. -/
theorem nnnorm_inner_le_nnnorm (x y : E) : ‖⟪x, y⟫‖₊ ≤ ‖x‖₊ * ‖y‖₊ :=
  norm_inner_le_norm x y
#align nnnorm_inner_le_nnnorm nnnorm_inner_le_nnnorm

/- warning: re_inner_le_norm -> re_inner_le_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align re_inner_le_norm re_inner_le_normₓ'. -/
theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ‖x‖ * ‖y‖ :=
  le_trans (re_le_norm (inner x y)) (norm_inner_le_norm x y)
#align re_inner_le_norm re_inner_le_norm

/- warning: abs_real_inner_le_norm -> abs_real_inner_le_norm is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))
Case conversion may be inaccurate. Consider using '#align abs_real_inner_le_norm abs_real_inner_le_normₓ'. -/
/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm (x y : F) : |⟪x, y⟫_ℝ| ≤ ‖x‖ * ‖y‖ :=
  (Real.norm_eq_abs _).ge.trans (norm_inner_le_norm x y)
#align abs_real_inner_le_norm abs_real_inner_le_norm

/- warning: real_inner_le_norm -> real_inner_le_norm is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.hasLe (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.instLEReal (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))
Case conversion may be inaccurate. Consider using '#align real_inner_le_norm real_inner_le_normₓ'. -/
/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ :=
  le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
#align real_inner_le_norm real_inner_le_norm

include 𝕜

variable (𝕜)

/- warning: parallelogram_law_with_norm -> parallelogram_law_with_norm is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y))))
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} Real (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y)) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y)) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y)))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) y) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) y))))
Case conversion may be inaccurate. Consider using '#align parallelogram_law_with_norm parallelogram_law_with_normₓ'. -/
theorem parallelogram_law_with_norm (x y : E) :
    ‖x + y‖ * ‖x + y‖ + ‖x - y‖ * ‖x - y‖ = 2 * (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) :=
  by
  simp only [← @inner_self_eq_norm_mul_norm 𝕜]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [re.map_add]
#align parallelogram_law_with_norm parallelogram_law_with_norm

/- warning: parallelogram_law_with_nnnorm -> parallelogram_law_with_nnnorm is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y)) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y)) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) x y)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (OfNat.ofNat.{0} NNReal 2 (OfNat.mk.{0} NNReal 2 (bit0.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))) (One.one.{0} NNReal (AddMonoidWithOne.toOne.{0} NNReal (AddCommMonoidWithOne.toAddMonoidWithOne.{0} NNReal (NonAssocSemiring.toAddCommMonoidWithOne.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring)))))))) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toHasAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) x) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) x)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (Distrib.toHasMul.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal NNReal.semiring))))) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) y) (NNNorm.nnnorm.{u2} E (SeminormedAddGroup.toNNNorm.{u2} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) y))))
but is expected to have type
  forall (𝕜 : Type.{u2}) {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), Eq.{1} NNReal (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) x y)))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (OfNat.ofNat.{0} NNReal 2 (instOfNat.{0} NNReal 2 (CanonicallyOrderedCommSemiring.toNatCast.{0} NNReal instNNRealCanonicallyOrderedCommSemiring) (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))) (HAdd.hAdd.{0, 0, 0} NNReal NNReal NNReal (instHAdd.{0} NNReal (Distrib.toAdd.{0} NNReal (NonUnitalNonAssocSemiring.toDistrib.{0} NNReal (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} NNReal (Semiring.toNonAssocSemiring.{0} NNReal instNNRealSemiring))))) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) x) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) x)) (HMul.hMul.{0, 0, 0} NNReal NNReal NNReal (instHMul.{0} NNReal (CanonicallyOrderedCommSemiring.toMul.{0} NNReal instNNRealCanonicallyOrderedCommSemiring)) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) y) (NNNorm.nnnorm.{u1} E (SeminormedAddGroup.toNNNorm.{u1} E (SeminormedAddCommGroup.toSeminormedAddGroup.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) y))))
Case conversion may be inaccurate. Consider using '#align parallelogram_law_with_nnnorm parallelogram_law_with_nnnormₓ'. -/
theorem parallelogram_law_with_nnnorm (x y : E) :
    ‖x + y‖₊ * ‖x + y‖₊ + ‖x - y‖₊ * ‖x - y‖₊ = 2 * (‖x‖₊ * ‖x‖₊ + ‖y‖₊ * ‖y‖₊) :=
  Subtype.ext <| parallelogram_law_with_norm 𝕜 x y
#align parallelogram_law_with_nnnorm parallelogram_law_with_nnnorm

variable {𝕜}

omit 𝕜

/- warning: re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two -> re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_twoₓ'. -/
/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 := by rw [@norm_add_mul_self 𝕜];
  ring
#align re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two

/- warning: re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two -> re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_twoₓ'. -/
/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 := by rw [@norm_sub_mul_self 𝕜];
  ring
#align re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two

/- warning: re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four -> re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_fourₓ'. -/
/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (‖x + y‖ * ‖x + y‖ - ‖x - y‖ * ‖x - y‖) / 4 := by
  rw [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜]; ring
#align re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four

/- warning: im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four -> im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_fourₓ'. -/
/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (‖x - IK • y‖ * ‖x - IK • y‖ - ‖x + IK • y‖ * ‖x + IK • y‖) / 4 := by
  simp only [@norm_add_mul_self 𝕜, @norm_sub_mul_self 𝕜, inner_smul_right, I_mul_re]; ring
#align im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four

/- warning: inner_eq_sum_norm_sq_div_four -> inner_eq_sum_norm_sq_div_four is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_eq_sum_norm_sq_div_four inner_eq_sum_norm_sq_div_fourₓ'. -/
/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = (‖x + y‖ ^ 2 - ‖x - y‖ ^ 2 + (‖x - IK • y‖ ^ 2 - ‖x + IK • y‖ ^ 2) * IK) / 4 :=
  by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_i_smul_mul_self_sub_norm_add_i_smul_mul_self_div_four]
  push_cast
  simp only [sq, ← mul_div_right_comm, ← add_div]
#align inner_eq_sum_norm_sq_div_four inner_eq_sum_norm_sq_div_four

/- warning: dist_div_norm_sq_smul -> dist_div_norm_sq_smul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align dist_div_norm_sq_smul dist_div_norm_sq_smulₓ'. -/
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
      (congr_arg sqrt <|
        by
        field_simp [sq, norm_sub_mul_self_real, norm_smul, real_inner_smul_left, inner_smul_right,
          Real.norm_of_nonneg (mul_self_nonneg _)]
        ring)
    _ = R ^ 2 / (‖x‖ * ‖y‖) * dist x y := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _),
        sqrt_sq (div_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))),
        dist_eq_norm]
    
#align dist_div_norm_sq_smul dist_div_norm_sq_smul

#print InnerProductSpace.toUniformConvexSpace /-
-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.toUniformConvexSpace : UniformConvexSpace F :=
  ⟨fun ε hε =>
    by
    refine'
      ⟨2 - sqrt (4 - ε ^ 2), sub_pos_of_lt <| (sqrt_lt' zero_lt_two).2 _, fun x hx y hy hxy => _⟩
    · norm_num
      exact pow_pos hε _
    rw [sub_sub_cancel]
    refine' le_sqrt_of_sq_le _
    rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm ℝ x y), ← sq ‖x - y‖, hx, hy]
    norm_num
    exact pow_le_pow_of_le_left hε.le hxy _⟩
#align inner_product_space.to_uniform_convex_space InnerProductSpace.toUniformConvexSpace
-/

section Complex

variable {V : Type _} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- warning: inner_map_polarization -> inner_map_polarization is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_map_polarization inner_map_polarizationₓ'. -/
/-- A complex polarization identity, with a linear map
-/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ +
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ -
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 :=
  by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring
#align inner_map_polarization inner_map_polarization

/- warning: inner_map_polarization' -> inner_map_polarization' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_map_polarization' inner_map_polarization'ₓ'. -/
theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ -
            Complex.I * ⟪T (x + Complex.I • y), x + Complex.I • y⟫_ℂ +
          Complex.I * ⟪T (x - Complex.I • y), x - Complex.I • y⟫_ℂ) /
        4 :=
  by
  simp only [map_add, map_sub, inner_add_left, inner_add_right, LinearMap.map_smul, inner_smul_left,
    inner_smul_right, Complex.conj_I, ← pow_two, Complex.I_sq, inner_sub_left, inner_sub_right,
    mul_add, ← mul_assoc, mul_neg, neg_neg, sub_neg_eq_add, one_mul, neg_one_mul, mul_sub, sub_sub]
  ring
#align inner_map_polarization' inner_map_polarization'

/- warning: inner_map_self_eq_zero -> inner_map_self_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_map_self_eq_zero inner_map_self_eq_zeroₓ'. -/
/-- A linear map `T` is zero, if and only if the identity `⟪T x, x⟫_ℂ = 0` holds for all `x`.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 :=
  by
  constructor
  · intro hT
    ext x
    simp only [LinearMap.zero_apply, ← @inner_self_eq_zero ℂ, inner_map_polarization, hT]
    norm_num
  · rintro rfl x
    simp only [LinearMap.zero_apply, inner_zero_left]
#align inner_map_self_eq_zero inner_map_self_eq_zero

/- warning: ext_inner_map -> ext_inner_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ext_inner_map ext_inner_mapₓ'. -/
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

variable {E' : Type _} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

variable {E'' : Type _} [NormedAddCommGroup E''] [InnerProductSpace 𝕜 E'']

/- warning: linear_isometry.inner_map_map -> LinearIsometry.inner_map_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.inner_map_map LinearIsometry.inner_map_mapₓ'. -/
/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [inner_eq_sum_norm_sq_div_four, ← f.norm_map]
#align linear_isometry.inner_map_map LinearIsometry.inner_map_map

/- warning: linear_isometry_equiv.inner_map_map -> LinearIsometryEquiv.inner_map_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry_equiv.inner_map_map LinearIsometryEquiv.inner_map_mapₓ'. -/
/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y
#align linear_isometry_equiv.inner_map_map LinearIsometryEquiv.inner_map_map

/- warning: linear_map.isometry_of_inner -> LinearMap.isometryOfInner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.isometry_of_inner LinearMap.isometryOfInnerₓ'. -/
/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by simp only [@norm_eq_sqrt_inner 𝕜, h]⟩
#align linear_map.isometry_of_inner LinearMap.isometryOfInner

/- warning: linear_map.coe_isometry_of_inner -> LinearMap.coe_isometryOfInner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.coe_isometry_of_inner LinearMap.coe_isometryOfInnerₓ'. -/
@[simp]
theorem LinearMap.coe_isometryOfInner (f : E →ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl
#align linear_map.coe_isometry_of_inner LinearMap.coe_isometryOfInner

/- warning: linear_map.isometry_of_inner_to_linear_map -> LinearMap.isometryOfInner_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.isometry_of_inner_to_linear_map LinearMap.isometryOfInner_toLinearMapₓ'. -/
@[simp]
theorem LinearMap.isometryOfInner_toLinearMap (f : E →ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearMap = f :=
  rfl
#align linear_map.isometry_of_inner_to_linear_map LinearMap.isometryOfInner_toLinearMap

/- warning: linear_equiv.isometry_of_inner -> LinearEquiv.isometryOfInner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.isometry_of_inner LinearEquiv.isometryOfInnerₓ'. -/
/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩
#align linear_equiv.isometry_of_inner LinearEquiv.isometryOfInner

/- warning: linear_equiv.coe_isometry_of_inner -> LinearEquiv.coe_isometryOfInner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_isometry_of_inner LinearEquiv.coe_isometryOfInnerₓ'. -/
@[simp]
theorem LinearEquiv.coe_isometryOfInner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl
#align linear_equiv.coe_isometry_of_inner LinearEquiv.coe_isometryOfInner

/- warning: linear_equiv.isometry_of_inner_to_linear_equiv -> LinearEquiv.isometryOfInner_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.isometry_of_inner_to_linear_equiv LinearEquiv.isometryOfInner_toLinearEquivₓ'. -/
@[simp]
theorem LinearEquiv.isometryOfInner_toLinearEquiv (f : E ≃ₗ[𝕜] E') (h) :
    (f.isometryOfInner h).toLinearEquiv = f :=
  rfl
#align linear_equiv.isometry_of_inner_to_linear_equiv LinearEquiv.isometryOfInner_toLinearEquiv

/- warning: linear_isometry.orthonormal_comp_iff -> LinearIsometry.orthonormal_comp_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_isometry.orthonormal_comp_iff LinearIsometry.orthonormal_comp_iffₓ'. -/
/-- A linear isometry preserves the property of being orthonormal. -/
theorem LinearIsometry.orthonormal_comp_iff {v : ι → E} (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) ↔ Orthonormal 𝕜 v := by
  classical simp_rw [orthonormal_iff_ite, LinearIsometry.inner_map_map]
#align linear_isometry.orthonormal_comp_iff LinearIsometry.orthonormal_comp_iff

/- warning: orthonormal.comp_linear_isometry -> Orthonormal.comp_linearIsometry is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.comp_linear_isometry Orthonormal.comp_linearIsometryₓ'. -/
/-- A linear isometry preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linearIsometry {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E →ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) := by rwa [f.orthonormal_comp_iff]
#align orthonormal.comp_linear_isometry Orthonormal.comp_linearIsometry

/- warning: orthonormal.comp_linear_isometry_equiv -> Orthonormal.comp_linearIsometryEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.comp_linear_isometry_equiv Orthonormal.comp_linearIsometryEquivₓ'. -/
/-- A linear isometric equivalence preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linearIsometryEquiv {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) :=
  hv.comp_linearIsometry f.toLinearIsometry
#align orthonormal.comp_linear_isometry_equiv Orthonormal.comp_linearIsometryEquiv

/- warning: orthonormal.map_linear_isometry_equiv -> Orthonormal.mapLinearIsometryEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.map_linear_isometry_equiv Orthonormal.mapLinearIsometryEquivₓ'. -/
/-- A linear isometric equivalence, applied with `basis.map`, preserves the property of being
orthonormal. -/
theorem Orthonormal.mapLinearIsometryEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (f : E ≃ₗᵢ[𝕜] E') : Orthonormal 𝕜 (v.map f.toLinearEquiv) :=
  hv.comp_linearIsometryEquiv f
#align orthonormal.map_linear_isometry_equiv Orthonormal.mapLinearIsometryEquiv

/- warning: linear_map.isometry_of_orthonormal -> LinearMap.isometryOfOrthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.isometry_of_orthonormal LinearMap.isometryOfOrthonormalₓ'. -/
/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
def LinearMap.isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← v.total_repr x, ← v.total_repr y, Finsupp.apply_total, Finsupp.apply_total,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_map.isometry_of_orthonormal LinearMap.isometryOfOrthonormal

/- warning: linear_map.coe_isometry_of_orthonormal -> LinearMap.coe_isometryOfOrthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.coe_isometry_of_orthonormal LinearMap.coe_isometryOfOrthonormalₓ'. -/
@[simp]
theorem LinearMap.coe_isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl
#align linear_map.coe_isometry_of_orthonormal LinearMap.coe_isometryOfOrthonormal

/- warning: linear_map.isometry_of_orthonormal_to_linear_map -> LinearMap.isometryOfOrthonormal_toLinearMap is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_map.isometry_of_orthonormal_to_linear_map LinearMap.isometryOfOrthonormal_toLinearMapₓ'. -/
@[simp]
theorem LinearMap.isometryOfOrthonormal_toLinearMap (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl
#align linear_map.isometry_of_orthonormal_to_linear_map LinearMap.isometryOfOrthonormal_toLinearMap

/- warning: linear_equiv.isometry_of_orthonormal -> LinearEquiv.isometryOfOrthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.isometry_of_orthonormal LinearEquiv.isometryOfOrthonormalₓ'. -/
/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.total_repr x, ← v.total_repr y, ← LinearEquiv.coe_coe, Finsupp.apply_total,
      Finsupp.apply_total, hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]
#align linear_equiv.isometry_of_orthonormal LinearEquiv.isometryOfOrthonormal

/- warning: linear_equiv.coe_isometry_of_orthonormal -> LinearEquiv.coe_isometryOfOrthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.coe_isometry_of_orthonormal LinearEquiv.coe_isometryOfOrthonormalₓ'. -/
@[simp]
theorem LinearEquiv.coe_isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl
#align linear_equiv.coe_isometry_of_orthonormal LinearEquiv.coe_isometryOfOrthonormal

/- warning: linear_equiv.isometry_of_orthonormal_to_linear_equiv -> LinearEquiv.isometryOfOrthonormal_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align linear_equiv.isometry_of_orthonormal_to_linear_equiv LinearEquiv.isometryOfOrthonormal_toLinearEquivₓ'. -/
@[simp]
theorem LinearEquiv.isometryOfOrthonormal_toLinearEquiv (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E}
    (hv : Orthonormal 𝕜 v) (hf : Orthonormal 𝕜 (f ∘ v)) :
    (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl
#align linear_equiv.isometry_of_orthonormal_to_linear_equiv LinearEquiv.isometryOfOrthonormal_toLinearEquiv

#print Orthonormal.equiv /-
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
-/

/- warning: orthonormal.equiv_to_linear_equiv -> Orthonormal.equiv_toLinearEquiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.equiv_to_linear_equiv Orthonormal.equiv_toLinearEquivₓ'. -/
@[simp]
theorem Orthonormal.equiv_toLinearEquiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    (hv.Equiv hv' e).toLinearEquiv = v.Equiv v' e :=
  rfl
#align orthonormal.equiv_to_linear_equiv Orthonormal.equiv_toLinearEquiv

/- warning: orthonormal.equiv_apply -> Orthonormal.equiv_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.equiv_apply Orthonormal.equiv_applyₓ'. -/
@[simp]
theorem Orthonormal.equiv_apply {ι' : Type _} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) :
    hv.Equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _
#align orthonormal.equiv_apply Orthonormal.equiv_apply

/- warning: orthonormal.equiv_refl -> Orthonormal.equiv_refl is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.equiv_refl Orthonormal.equiv_reflₓ'. -/
@[simp]
theorem Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) :
    hv.Equiv hv (Equiv.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [Orthonormal.equiv_apply, Equiv.coe_refl, id.def, LinearIsometryEquiv.coe_refl]
#align orthonormal.equiv_refl Orthonormal.equiv_refl

/- warning: orthonormal.equiv_symm -> Orthonormal.equiv_symm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.equiv_symm Orthonormal.equiv_symmₓ'. -/
@[simp]
theorem Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.Equiv hv' e).symm = hv'.Equiv hv e.symm :=
  v'.ext_linearIsometryEquiv fun i =>
    (hv.Equiv hv' e).Injective <| by
      simp only [LinearIsometryEquiv.apply_symm_apply, Orthonormal.equiv_apply, e.apply_symm_apply]
#align orthonormal.equiv_symm Orthonormal.equiv_symm

/- warning: orthonormal.equiv_trans -> Orthonormal.equiv_trans is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.equiv_trans Orthonormal.equiv_transₓ'. -/
@[simp]
theorem Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' : Orthonormal 𝕜 v'')
    (e' : ι' ≃ ι'') : (hv.Equiv hv' e).trans (hv'.Equiv hv'' e') = hv.Equiv hv'' (e.trans e') :=
  v.ext_linearIsometryEquiv fun i => by
    simp only [LinearIsometryEquiv.trans_apply, Orthonormal.equiv_apply, e.coe_trans]
#align orthonormal.equiv_trans Orthonormal.equiv_trans

/- warning: orthonormal.map_equiv -> Orthonormal.map_equiv is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.map_equiv Orthonormal.map_equivₓ'. -/
theorem Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') :
    v.map (hv.Equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.mapEquiv _ _
#align orthonormal.map_equiv Orthonormal.map_equiv

end

/- warning: real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two -> real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_twoₓ'. -/
/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x + y‖ * ‖x + y‖ - ‖x‖ * ‖x‖ - ‖y‖ * ‖y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y
#align real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two

/- warning: real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two -> real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.hasSub) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)))) (OfNat.ofNat.{0} Real 2 (OfNat.mk.{0} Real 2 (bit0.{0} Real Real.hasAdd (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (HSub.hSub.{0, 0, 0} Real Real Real (instHSub.{0} Real Real.instSubReal) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)))) (OfNat.ofNat.{0} Real 2 (instOfNat.{0} Real 2 Real.natCast (instAtLeastTwoHAddNatInstHAddInstAddNatOfNat (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))))
Case conversion may be inaccurate. Consider using '#align real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_twoₓ'. -/
/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ - ‖x - y‖ * ‖x - y‖) / 2 :=
  re_to_real.symm.trans <|
    re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y
#align real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two

/- warning: norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero -> norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zeroₓ'. -/
/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
  by
  rw [@norm_add_mul_self ℝ, add_right_cancel_iff, add_right_eq_self, mul_eq_zero]
  norm_num
#align norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero

/- warning: norm_add_eq_sqrt_iff_real_inner_eq_zero -> norm_add_eq_sqrt_iff_real_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align norm_add_eq_sqrt_iff_real_inner_eq_zero norm_add_eq_sqrt_iff_real_inner_eq_zeroₓ'. -/
/-- Pythagorean theorem, if-and-if vector inner product form using square roots. -/
theorem norm_add_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x + y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
    sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]
#align norm_add_eq_sqrt_iff_real_inner_eq_zero norm_add_eq_sqrt_iff_real_inner_eq_zero

/- warning: norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero -> norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (x : E) (y : E), (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y)) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) y) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) y))))
Case conversion may be inaccurate. Consider using '#align norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zeroₓ'. -/
/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  by
  rw [@norm_add_mul_self 𝕜, add_right_cancel_iff, add_right_eq_self, mul_eq_zero]
  apply Or.inr
  simp only [h, zero_re']
#align norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero

/- warning: norm_add_sq_eq_norm_sq_add_norm_sq_real -> norm_add_sq_eq_norm_sq_add_norm_sq_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))))
Case conversion may be inaccurate. Consider using '#align norm_add_sq_eq_norm_sq_add_norm_sq_real norm_add_sq_eq_norm_sq_add_norm_sq_realₓ'. -/
/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x + y‖ * ‖x + y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h
#align norm_add_sq_eq_norm_sq_add_norm_sq_real norm_add_sq_eq_norm_sq_add_norm_sq_real

/- warning: norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero -> norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zeroₓ'. -/
/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ = 0 :=
  by
  rw [@norm_sub_mul_self ℝ, add_right_cancel_iff, sub_eq_add_neg, add_right_eq_self, neg_eq_zero,
    mul_eq_zero]
  norm_num
#align norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero

/- warning: norm_sub_eq_sqrt_iff_real_inner_eq_zero -> norm_sub_eq_sqrt_iff_real_inner_eq_zero is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Real.sqrt (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))))) (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)))
Case conversion may be inaccurate. Consider using '#align norm_sub_eq_sqrt_iff_real_inner_eq_zero norm_sub_eq_sqrt_iff_real_inner_eq_zeroₓ'. -/
/-- Pythagorean theorem, subtracting vectors, if-and-if vector inner product form using square
roots. -/
theorem norm_sub_eq_sqrt_iff_real_inner_eq_zero {x y : F} :
    ‖x - y‖ = sqrt (‖x‖ * ‖x‖ + ‖y‖ * ‖y‖) ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [← norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero, eq_comm,
    sqrt_eq_iff_mul_self_eq (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)) (norm_nonneg _)]
#align norm_sub_eq_sqrt_iff_real_inner_eq_zero norm_sub_eq_sqrt_iff_real_inner_eq_zero

/- warning: norm_sub_sq_eq_norm_sq_add_norm_sq_real -> norm_sub_sq_eq_norm_sq_add_norm_sq_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.hasAdd) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y))) (HAdd.hAdd.{0, 0, 0} Real Real Real (instHAdd.{0} Real Real.instAddReal) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))))
Case conversion may be inaccurate. Consider using '#align norm_sub_sq_eq_norm_sq_add_norm_sq_real norm_sub_sq_eq_norm_sq_add_norm_sq_realₓ'. -/
/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ‖x - y‖ * ‖x - y‖ = ‖x‖ * ‖x‖ + ‖y‖ * ‖y‖ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h
#align norm_sub_sq_eq_norm_sq_add_norm_sq_real norm_sub_sq_eq_norm_sq_add_norm_sq_real

/- warning: real_inner_add_sub_eq_zero_iff -> real_inner_add_sub_eq_zero_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toHasAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toHasSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HAdd.hAdd.{u1, u1, u1} F F F (instHAdd.{u1} F (AddZeroClass.toAdd.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))))) x y) (HSub.hSub.{u1, u1, u1} F F F (instHSub.{u1} F (SubNegMonoid.toSub.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4))))) x y)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))
Case conversion may be inaccurate. Consider using '#align real_inner_add_sub_eq_zero_iff real_inner_add_sub_eq_zero_iffₓ'. -/
/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ‖x‖ = ‖y‖ :=
  by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [← @inner_self_eq_norm_mul_norm ℝ, inner_add_left, inner_sub_right, real_inner_comm y x,
    sub_eq_zero, re_to_real]
  constructor
  · intro h
    rw [add_comm] at h
    linarith
  · intro h
    linarith
#align real_inner_add_sub_eq_zero_iff real_inner_add_sub_eq_zero_iff

/- warning: norm_sub_eq_norm_add -> norm_sub_eq_norm_add is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {v : E} {w : E}, (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) v w) (OfNat.ofNat.{u1} 𝕜 0 (OfNat.mk.{u1} 𝕜 0 (Zero.zero.{u1} 𝕜 (MulZeroClass.toHasZero.{u1} 𝕜 (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} 𝕜 (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))))))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HSub.hSub.{u2, u2, u2} E E E (instHSub.{u2} E (SubNegMonoid.toHasSub.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))) w v)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) (HAdd.hAdd.{u2, u2, u2} E E E (instHAdd.{u2} E (AddZeroClass.toHasAdd.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2))))))) w v)))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {v : E} {w : E}, (Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) v w) (OfNat.ofNat.{u2} 𝕜 0 (Zero.toOfNat0.{u2} 𝕜 (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))))) -> (Eq.{1} Real (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HSub.hSub.{u1, u1, u1} E E E (instHSub.{u1} E (SubNegMonoid.toSub.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))) w v)) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) (HAdd.hAdd.{u1, u1, u1} E E E (instHAdd.{u1} E (AddZeroClass.toAdd.{u1} E (AddMonoid.toAddZeroClass.{u1} E (SubNegMonoid.toAddMonoid.{u1} E (AddGroup.toSubNegMonoid.{u1} E (NormedAddGroup.toAddGroup.{u1} E (NormedAddCommGroup.toNormedAddGroup.{u1} E _inst_2))))))) w v)))
Case conversion may be inaccurate. Consider using '#align norm_sub_eq_norm_add norm_sub_eq_norm_addₓ'. -/
/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ‖w - v‖ = ‖w + v‖ :=
  by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [h, ← @inner_self_eq_norm_mul_norm 𝕜, sub_neg_eq_add, sub_zero, map_sub, zero_re',
    zero_sub, add_zero, map_add, inner_add_right, inner_sub_left, inner_sub_right, inner_re_symm,
    zero_add]
#align norm_sub_eq_norm_add norm_sub_eq_norm_add

/- warning: abs_real_inner_div_norm_mul_norm_le_one -> abs_real_inner_div_norm_mul_norm_le_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.hasLe (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), LE.le.{0} Real Real.instLEReal (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))
Case conversion may be inaccurate. Consider using '#align abs_real_inner_div_norm_mul_norm_le_one abs_real_inner_div_norm_mul_norm_le_oneₓ'. -/
/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| ≤ 1 :=
  by
  rw [abs_div, abs_mul, abs_norm, abs_norm]
  exact div_le_one_of_le (abs_real_inner_le_norm x y) (by positivity)
#align abs_real_inner_div_norm_mul_norm_le_one abs_real_inner_div_norm_mul_norm_le_one

/- warning: real_inner_smul_self_left -> real_inner_smul_self_left is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x) x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x) x) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)))
Case conversion may be inaccurate. Consider using '#align real_inner_smul_self_left real_inner_smul_self_leftₓ'. -/
/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [real_inner_smul_left, ← real_inner_self_eq_norm_mul_norm]
#align real_inner_smul_self_left real_inner_smul_self_left

/- warning: real_inner_smul_self_right -> real_inner_smul_self_right is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) r (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x)))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (r : Real), Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) r (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x)))
Case conversion may be inaccurate. Consider using '#align real_inner_smul_self_right real_inner_smul_self_rightₓ'. -/
/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (‖x‖ * ‖x‖) := by
  rw [inner_smul_right, ← real_inner_self_eq_norm_mul_norm]
#align real_inner_smul_self_right real_inner_smul_self_right

/- warning: norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul -> norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mulₓ'. -/
/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0)
    (hr : r ≠ 0) : ‖⟪x, r • x⟫‖ / (‖x‖ * ‖r • x‖) = 1 :=
  by
  have hx' : ‖x‖ ≠ 0 := by simp [hx]
  have hr' : ‖r‖ ≠ 0 := by simp [hr]
  rw [inner_smul_right, norm_mul, ← inner_self_re_eq_norm, inner_self_eq_norm_mul_norm, norm_smul]
  rw [← mul_assoc, ← div_div, mul_div_cancel _ hx', ← div_div, mul_comm, mul_div_cancel _ hr',
    div_self hx']
#align norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul

/- warning: abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul -> abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mulₓ'. -/
/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ}
    (hx : x ≠ 0) (hr : r ≠ 0) : |⟪x, r • x⟫_ℝ| / (‖x‖ * ‖r • x‖) = 1 :=
  norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
#align abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul

/- warning: real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul -> real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {r : Real}, (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4)))))))))) -> (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {r : Real}, (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))) -> (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))
Case conversion may be inaccurate. Consider using '#align real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mulₓ'. -/
/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : 0 < r) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = 1 :=
  by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ (|r|),
    mul_assoc, abs_of_nonneg hr.le, div_self]
  exact mul_ne_zero hr.ne' (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))
#align real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul

/- warning: real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul -> real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {r : Real}, (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4)))))))))) -> (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)))) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {r : Real}, (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))) -> (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) -> (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)))) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))))
Case conversion may be inaccurate. Consider using '#align real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mulₓ'. -/
/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0)
    (hr : r < 0) : ⟪x, r • x⟫_ℝ / (‖x‖ * ‖r • x‖) = -1 :=
  by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ‖x‖, mul_comm _ (|r|),
    mul_assoc, abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self]
  exact mul_ne_zero hr.ne (mul_self_ne_zero.2 (norm_ne_zero_iff.2 hx))
#align real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul

/- warning: norm_inner_eq_norm_tfae -> norm_inner_eq_norm_tfae is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_inner_eq_norm_tfae norm_inner_eq_norm_tfaeₓ'. -/
theorem norm_inner_eq_norm_tfae (x y : E) :
    TFAE
      [‖⟪x, y⟫‖ = ‖x‖ * ‖y‖, x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫) • x, x = 0 ∨ ∃ r : 𝕜, y = r • x,
        x = 0 ∨ y ∈ 𝕜 ∙ x] :=
  by
  tfae_have 1 → 2
  · refine' fun h => or_iff_not_imp_left.2 fun hx₀ => _
    have : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hx₀)
    rw [← sq_eq_sq (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), mul_pow, ←
      mul_right_inj' this, eq_comm, ← sub_eq_zero, ← mul_sub] at h
    simp only [@norm_sq_eq_inner 𝕜] at h
    letI : InnerProductSpace.Core 𝕜 E := InnerProductSpace.toCore
    erw [← InnerProductSpace.Core.cauchy_schwarz_aux, InnerProductSpace.Core.normSq_eq_zero,
      sub_eq_zero] at h
    rw [div_eq_inv_mul, mul_smul, h, inv_smul_smul₀]
    rwa [inner_self_ne_zero]
  tfae_have 2 → 3; exact fun h => h.imp_right fun h' => ⟨_, h'⟩
  tfae_have 3 → 1
  ·
    rintro (rfl | ⟨r, rfl⟩) <;>
      simp [inner_smul_right, norm_smul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_mul_norm,
        sq, mul_left_comm]
  tfae_have 3 ↔ 4; · simp only [Submodule.mem_span_singleton, eq_comm]
  tfae_finish
#align norm_inner_eq_norm_tfae norm_inner_eq_norm_tfae

/- warning: norm_inner_eq_norm_iff -> norm_inner_eq_norm_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_inner_eq_norm_iff norm_inner_eq_norm_iffₓ'. -/
/-- If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem norm_inner_eq_norm_iff {x y : E} (hx₀ : x ≠ 0) (hy₀ : y ≠ 0) :
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  calc
    ‖⟪x, y⟫‖ = ‖x‖ * ‖y‖ ↔ x = 0 ∨ ∃ r : 𝕜, y = r • x :=
      (@norm_inner_eq_norm_tfae 𝕜 _ _ _ _ x y).out 0 2
    _ ↔ ∃ r : 𝕜, y = r • x := (or_iff_right hx₀)
    _ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
      ⟨fun ⟨r, h⟩ => ⟨r, fun hr₀ => hy₀ <| h.symm ▸ smul_eq_zero.2 <| Or.inl hr₀, h⟩,
        fun ⟨r, hr₀, h⟩ => ⟨r, h⟩⟩
    
#align norm_inner_eq_norm_iff norm_inner_eq_norm_iff

/- warning: norm_inner_div_norm_mul_norm_eq_one_iff -> norm_inner_div_norm_mul_norm_eq_one_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align norm_inner_div_norm_mul_norm_eq_one_iff norm_inner_div_norm_mul_norm_eq_one_iffₓ'. -/
/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem norm_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    ‖⟪x, y⟫ / (‖x‖ * ‖y‖)‖ = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x :=
  by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simpa [h₀] using h
    have hy₀ : y ≠ 0 := fun h₀ => by simpa [h₀] using h
    refine' ⟨hx₀, (norm_inner_eq_norm_iff hx₀ hy₀).1 <| eq_of_div_eq_one _⟩
    simpa using h
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    simp only [norm_div, norm_mul, norm_of_real, abs_norm]
    exact norm_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
#align norm_inner_div_norm_mul_norm_eq_one_iff norm_inner_div_norm_mul_norm_eq_one_iff

/- warning: abs_real_inner_div_norm_mul_norm_eq_one_iff -> abs_real_inner_div_norm_mul_norm_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.hasNeg Real.hasSup) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y)))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4)))))))))) (Exists.{1} Real (fun (r : Real) => And (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} F y (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (Abs.abs.{0} Real (Neg.toHasAbs.{0} Real Real.instNegReal Real.instSupReal) (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y)))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))) (Exists.{1} Real (fun (r : Real) => And (Ne.{1} Real r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} F y (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)))))
Case conversion may be inaccurate. Consider using '#align abs_real_inner_div_norm_mul_norm_eq_one_iff abs_real_inner_div_norm_mul_norm_eq_one_iffₓ'. -/
/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    |⟪x, y⟫_ℝ / (‖x‖ * ‖y‖)| = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ y = r • x :=
  @norm_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ _ x y
#align abs_real_inner_div_norm_mul_norm_eq_one_iff abs_real_inner_div_norm_mul_norm_eq_one_iff

/- warning: inner_eq_norm_mul_iff_div -> inner_eq_norm_mul_iff_div is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (OfNat.mk.{u2} E 0 (Zero.zero.{u2} E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (SubNegMonoid.toAddMonoid.{u2} E (AddGroup.toSubNegMonoid.{u2} E (NormedAddGroup.toAddGroup.{u2} E (NormedAddCommGroup.toNormedAddGroup.{u2} E _inst_2)))))))))) -> (Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y)))) (Eq.{succ u2} E (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (DivInvMonoid.toHasDiv.{u1} 𝕜 (DivisionRing.toDivInvMonoid.{u1} 𝕜 (NormedDivisionRing.toDivisionRing.{u1} 𝕜 (NormedField.toNormedDivisionRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y)) ((fun (a : Type) (b : Type.{u1}) [self : HasLiftT.{1, succ u1} a b] => self.0) Real 𝕜 (HasLiftT.mk.{1, succ u1} Real 𝕜 (CoeTCₓ.coe.{1, succ u1} Real 𝕜 (IsROrC.algebraMapCoe.{u1} 𝕜 _inst_1))) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x))) x) y))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (Ne.{succ u2} E x (OfNat.ofNat.{u2} E 0 (Zero.toOfNat0.{u2} E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2))))))))) -> (Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (NonUnitalNonAssocRing.toMul.{u1} 𝕜 (NonAssocRing.toNonUnitalNonAssocRing.{u1} 𝕜 (Ring.toNonAssocRing.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x)) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) y)))) (Eq.{succ u2} E (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))))) (HDiv.hDiv.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHDiv.{u1} 𝕜 (Field.toDiv.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) y)) (IsROrC.ofReal.{u1} 𝕜 _inst_1 (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x))) x) y))
Case conversion may be inaccurate. Consider using '#align inner_eq_norm_mul_iff_div inner_eq_norm_mul_iff_divₓ'. -/
theorem inner_eq_norm_mul_iff_div {x y : E} (h₀ : x ≠ 0) :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ / ‖x‖ : 𝕜) • x = y :=
  by
  have h₀' := h₀
  rw [← norm_ne_zero_iff, Ne.def, ← @of_real_eq_zero 𝕜] at h₀'
  constructor <;> intro h
  · have : x = 0 ∨ y = (⟪x, y⟫ / ⟪x, x⟫ : 𝕜) • x :=
      ((@norm_inner_eq_norm_tfae 𝕜 _ _ _ _ x y).out 0 1).1 (by simp [h])
    rw [this.resolve_left h₀, h]
    simp [norm_smul, inner_self_ofReal_norm, h₀']
  · conv_lhs => rw [← h, inner_smul_right, inner_self_eq_norm_sq_to_K]
    field_simp [sq, mul_left_comm]
#align inner_eq_norm_mul_iff_div inner_eq_norm_mul_iff_div

/- warning: inner_eq_norm_mul_iff -> inner_eq_norm_mul_iff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_eq_norm_mul_iff inner_eq_norm_mul_iffₓ'. -/
/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff {x y : E} :
    ⟪x, y⟫ = (‖x‖ : 𝕜) * ‖y‖ ↔ (‖y‖ : 𝕜) • x = (‖x‖ : 𝕜) • y :=
  by
  rcases eq_or_ne x 0 with (rfl | h₀)
  · simp
  · rw [inner_eq_norm_mul_iff_div h₀, div_eq_inv_mul, mul_smul, inv_smul_eq_iff₀]
    rwa [Ne.def, of_real_eq_zero, norm_eq_zero]
#align inner_eq_norm_mul_iff inner_eq_norm_mul_iff

/- warning: inner_eq_norm_mul_iff_real -> inner_eq_norm_mul_iff_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (Eq.{succ u1} F (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) x) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (Eq.{1} Real (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (Eq.{succ u1} F (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) x) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) y))
Case conversion may be inaccurate. Consider using '#align inner_eq_norm_mul_iff_real inner_eq_norm_mul_iff_realₓ'. -/
/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ‖x‖ * ‖y‖`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `norm_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ‖x‖ * ‖y‖`. -/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ‖x‖ * ‖y‖ ↔ ‖y‖ • x = ‖x‖ • y :=
  inner_eq_norm_mul_iff
#align inner_eq_norm_mul_iff_real inner_eq_norm_mul_iff_real

/- warning: real_inner_div_norm_mul_norm_eq_one_iff -> real_inner_div_norm_mul_norm_eq_one_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4)))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero))) r) (Eq.{succ u1} F y (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal)) r) (Eq.{succ u1} F y (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)))))
Case conversion may be inaccurate. Consider using '#align real_inner_div_norm_mul_norm_eq_one_iff real_inner_div_norm_mul_norm_eq_one_iffₓ'. -/
/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x :=
  by
  constructor
  · intro h
    have hx₀ : x ≠ 0 := fun h₀ => by simpa [h₀] using h
    have hy₀ : y ≠ 0 := fun h₀ => by simpa [h₀] using h
    refine' ⟨hx₀, ‖y‖ / ‖x‖, div_pos (norm_pos_iff.2 hy₀) (norm_pos_iff.2 hx₀), _⟩
    exact ((inner_eq_norm_mul_iff_div hx₀).1 (eq_of_div_eq_one h)).symm
  · rintro ⟨hx, ⟨r, ⟨hr, rfl⟩⟩⟩
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr
#align real_inner_div_norm_mul_norm_eq_one_iff real_inner_div_norm_mul_norm_eq_one_iff

/- warning: real_inner_div_norm_mul_norm_eq_neg_one_iff -> real_inner_div_norm_mul_norm_eq_neg_one_iff is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (DivInvMonoid.toHasDiv.{0} Real (DivisionRing.toDivInvMonoid.{0} Real Real.divisionRing))) (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (Neg.neg.{0} Real Real.hasNeg (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne))))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (OfNat.mk.{u1} F 0 (Zero.zero.{u1} F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (SubNegMonoid.toAddMonoid.{u1} F (AddGroup.toSubNegMonoid.{u1} F (NormedAddGroup.toAddGroup.{u1} F (NormedAddCommGroup.toNormedAddGroup.{u1} F _inst_4)))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.hasLt r (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))) (Eq.{succ u1} F y (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) r x)))))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] (x : F) (y : F), Iff (Eq.{1} Real (HDiv.hDiv.{0, 0, 0} Real Real Real (instHDiv.{0} Real (LinearOrderedField.toDiv.{0} Real Real.instLinearOrderedFieldReal)) (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (Neg.neg.{0} Real Real.instNegReal (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal)))) (And (Ne.{succ u1} F x (OfNat.ofNat.{u1} F 0 (Zero.toOfNat0.{u1} F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4))))))))) (Exists.{1} Real (fun (r : Real) => And (LT.lt.{0} Real Real.instLTReal r (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))) (Eq.{succ u1} F y (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) r x)))))
Case conversion may be inaccurate. Consider using '#align real_inner_div_norm_mul_norm_eq_neg_one_iff real_inner_div_norm_mul_norm_eq_neg_one_iffₓ'. -/
/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (‖x‖ * ‖y‖) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x :=
  by
  rw [← neg_eq_iff_eq_neg, ← neg_div, ← inner_neg_right, ← norm_neg y,
    real_inner_div_norm_mul_norm_eq_one_iff, (@neg_surjective ℝ _).exists]
  refine' iff.rfl.and (exists_congr fun r => _)
  rw [neg_pos, neg_smul, neg_inj]
#align real_inner_div_norm_mul_norm_eq_neg_one_iff real_inner_div_norm_mul_norm_eq_neg_one_iff

/- warning: inner_eq_one_iff_of_norm_one -> inner_eq_one_iff_of_norm_one is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u1} 𝕜 1 (OfNat.mk.{u1} 𝕜 1 (One.one.{u1} 𝕜 (AddMonoidWithOne.toOne.{u1} 𝕜 (AddGroupWithOne.toAddMonoidWithOne.{u1} 𝕜 (AddCommGroupWithOne.toAddGroupWithOne.{u1} 𝕜 (Ring.toAddCommGroupWithOne.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))))) (Eq.{succ u2} E x y))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {x : E} {y : E}, (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x y) (OfNat.ofNat.{u1} 𝕜 1 (One.toOfNat1.{u1} 𝕜 (Semiring.toOne.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (Eq.{succ u2} E x y))
Case conversion may be inaccurate. Consider using '#align inner_eq_one_iff_of_norm_one inner_eq_one_iff_of_norm_oneₓ'. -/
/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_one_iff_of_norm_one {x y : E} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) : ⟪x, y⟫ = 1 ↔ x = y :=
  by convert inner_eq_norm_mul_iff using 2 <;> simp [hx, hy]
#align inner_eq_one_iff_of_norm_one inner_eq_one_iff_of_norm_one

/- warning: inner_lt_norm_mul_iff_real -> inner_lt_norm_mul_iff_real is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (LT.lt.{0} Real Real.hasLt (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y))) (Ne.{succ u1} F (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) x) (SMul.smul.{0, u1} Real F (SMulZeroClass.toHasSmul.{0, u1} Real F (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSmulZeroClass.{0, u1} Real F (MulZeroClass.toHasZero.{0} Real (MulZeroOneClass.toMulZeroClass.{0} Real (MonoidWithZero.toMulZeroOneClass.{0} Real (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F (Semiring.toMonoidWithZero.{0} Real (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC))))))) (AddZeroClass.toHasZero.{u1} F (AddMonoid.toAddZeroClass.{u1} F (AddCommMonoid.toAddMonoid.{u1} F (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F (Ring.toSemiring.{0} Real (NormedRing.toRing.{0} Real (NormedCommRing.toNormedRing.{0} Real (NormedField.toNormedCommRing.{0} Real (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)))))) (AddCommGroup.toAddCommMonoid.{u1} F (SeminormedAddCommGroup.toAddCommGroup.{u1} F (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4))) (NormedSpace.toModule.{0, u1} Real F (DenselyNormedField.toNormedField.{0} Real (IsROrC.toDenselyNormedField.{0} Real Real.isROrC)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5)))))) (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, Iff (LT.lt.{0} Real Real.instLTReal (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y))) (Ne.{succ u1} F (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) x) (HSMul.hSMul.{0, u1, u1} Real F F (instHSMul.{0, u1} Real F (SMulZeroClass.toSMul.{0, u1} Real F (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (SMulWithZero.toSMulZeroClass.{0, u1} Real F Real.instZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (MulActionWithZero.toSMulWithZero.{0, u1} Real F Real.instMonoidWithZeroReal (NegZeroClass.toZero.{u1} F (SubNegZeroMonoid.toNegZeroClass.{u1} F (SubtractionMonoid.toSubNegZeroMonoid.{u1} F (SubtractionCommMonoid.toSubtractionMonoid.{u1} F (AddCommGroup.toDivisionAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)))))) (Module.toMulActionWithZero.{0, u1} Real F Real.semiring (AddCommGroup.toAddCommMonoid.{u1} F (NormedAddCommGroup.toAddCommGroup.{u1} F _inst_4)) (NormedSpace.toModule.{0, u1} Real F Real.normedField (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} F _inst_4) (InnerProductSpace.toNormedSpace.{0, u1} Real F Real.isROrC _inst_4 _inst_5))))))) (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) y))
Case conversion may be inaccurate. Consider using '#align inner_lt_norm_mul_iff_real inner_lt_norm_mul_iff_realₓ'. -/
theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ‖y‖ • x ≠ ‖x‖ • y :=
  calc
    ⟪x, y⟫_ℝ < ‖x‖ * ‖y‖ ↔ ⟪x, y⟫_ℝ ≠ ‖x‖ * ‖y‖ :=
      ⟨ne_of_lt, lt_of_le_of_ne (real_inner_le_norm _ _)⟩
    _ ↔ ‖y‖ • x ≠ ‖x‖ • y := not_congr inner_eq_norm_mul_iff_real
    
#align inner_lt_norm_mul_iff_real inner_lt_norm_mul_iff_real

/- warning: inner_lt_one_iff_real_of_norm_one -> inner_lt_one_iff_real_of_norm_one is a dubious translation:
lean 3 declaration is
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toHasNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) -> (Iff (LT.lt.{0} Real Real.hasLt (Inner.inner.{0, u1} Real F (InnerProductSpace.toHasInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 1 (OfNat.mk.{0} Real 1 (One.one.{0} Real Real.hasOne)))) (Ne.{succ u1} F x y))
but is expected to have type
  forall {F : Type.{u1}} [_inst_4 : NormedAddCommGroup.{u1} F] [_inst_5 : InnerProductSpace.{0, u1} Real F Real.isROrC _inst_4] {x : F} {y : F}, (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) x) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Eq.{1} Real (Norm.norm.{u1} F (NormedAddCommGroup.toNorm.{u1} F _inst_4) y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) -> (Iff (LT.lt.{0} Real Real.instLTReal (Inner.inner.{0, u1} Real F (InnerProductSpace.toInner.{0, u1} Real F Real.isROrC _inst_4 _inst_5) x y) (OfNat.ofNat.{0} Real 1 (One.toOfNat1.{0} Real Real.instOneReal))) (Ne.{succ u1} F x y))
Case conversion may be inaccurate. Consider using '#align inner_lt_one_iff_real_of_norm_one inner_lt_one_iff_real_of_norm_oneₓ'. -/
/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by convert inner_lt_norm_mul_iff_real <;> simp [hx, hy]
#align inner_lt_one_iff_real_of_norm_one inner_lt_one_iff_real_of_norm_one

/- warning: inner_sum_smul_sum_smul_of_sum_eq_zero -> inner_sum_smul_sum_smul_of_sum_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_sum_smul_sum_smul_of_sum_eq_zero inner_sum_smul_sum_smul_of_sum_eq_zeroₓ'. -/
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
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h₁, h₂, MulZeroClass.zero_mul,
    MulZeroClass.mul_zero, Finset.sum_const_zero, zero_add, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]
#align inner_sum_smul_sum_smul_of_sum_eq_zero inner_sum_smul_sum_smul_of_sum_eq_zero

variable (𝕜)

#print innerₛₗ /-
/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) inner_add_left (fun _ _ _ => inner_smul_left _ _ _)
    inner_add_right fun _ _ _ => inner_smul_right _ _ _
#align innerₛₗ innerₛₗ
-/

/- warning: innerₛₗ_apply_coe -> innerₛₗ_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerₛₗ_apply_coe innerₛₗ_apply_coeₓ'. -/
@[simp]
theorem innerₛₗ_apply_coe (v : E) : ⇑(innerₛₗ 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl
#align innerₛₗ_apply_coe innerₛₗ_apply_coe

/- warning: innerₛₗ_apply -> innerₛₗ_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerₛₗ_apply innerₛₗ_applyₓ'. -/
@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ 𝕜 v w = ⟪v, w⟫ :=
  rfl
#align innerₛₗ_apply innerₛₗ_apply

#print innerSL /-
/-- The inner product as a continuous sesquilinear map. Note that `to_dual_map` (resp. `to_dual`)
in `inner_product_space.dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ (innerₛₗ 𝕜) 1 fun x y => by
    simp only [norm_inner_le_norm, one_mul, innerₛₗ_apply]
#align innerSL innerSL
-/

/- warning: innerSL_apply_coe -> innerSL_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerSL_apply_coe innerSL_apply_coeₓ'. -/
@[simp]
theorem innerSL_apply_coe (v : E) : ⇑(innerSL 𝕜 v) = fun w => ⟪v, w⟫ :=
  rfl
#align innerSL_apply_coe innerSL_apply_coe

/- warning: innerSL_apply -> innerSL_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerSL_apply innerSL_applyₓ'. -/
@[simp]
theorem innerSL_apply (v w : E) : innerSL 𝕜 v w = ⟪v, w⟫ :=
  rfl
#align innerSL_apply innerSL_apply

/- warning: innerSL_apply_norm -> innerSL_apply_norm is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerSL_apply_norm innerSL_apply_normₓ'. -/
/-- `innerSL` is an isometry. Note that the associated `linear_isometry` is defined in
`inner_product_space.dual` as `to_dual_map`.  -/
@[simp]
theorem innerSL_apply_norm (x : E) : ‖innerSL 𝕜 x‖ = ‖x‖ :=
  by
  refine'
    le_antisymm ((innerSL 𝕜 x).opNorm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) _
  rcases eq_or_ne x 0 with (rfl | h)
  · simp
  · refine' (mul_le_mul_right (norm_pos_iff.2 h)).mp _
    calc
      ‖x‖ * ‖x‖ = ‖(⟪x, x⟫ : 𝕜)‖ := by
        rw [← sq, inner_self_eq_norm_sq_to_K, norm_pow, norm_of_real, abs_norm]
      _ ≤ ‖innerSL 𝕜 x‖ * ‖x‖ := (innerSL 𝕜 x).le_opNorm _
      
#align innerSL_apply_norm innerSL_apply_norm

#print innerSLFlip /-
/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _
    (innerSL 𝕜)
#align innerSL_flip innerSLFlip
-/

/- warning: innerSL_flip_apply -> innerSLFlip_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align innerSL_flip_apply innerSLFlip_applyₓ'. -/
@[simp]
theorem innerSLFlip_apply (x y : E) : innerSLFlip 𝕜 x y = ⟪y, x⟫ :=
  rfl
#align innerSL_flip_apply innerSLFlip_apply

variable {𝕜}

namespace ContinuousLinearMap

variable {E' : Type _} [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E']

#print ContinuousLinearMap.toSesqForm /-
/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `λ x y, ⟪x, A y⟫`, given
as a continuous linear map. -/
def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  ↑(ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) (innerSLFlip 𝕜)
#align continuous_linear_map.to_sesq_form ContinuousLinearMap.toSesqForm
-/

/- warning: continuous_linear_map.to_sesq_form_apply_coe -> ContinuousLinearMap.toSesqForm_apply_coe is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_sesq_form_apply_coe ContinuousLinearMap.toSesqForm_apply_coeₓ'. -/
@[simp]
theorem toSesqForm_apply_coe (f : E →L[𝕜] E') (x : E') : toSesqForm f x = (innerSL 𝕜 x).comp f :=
  rfl
#align continuous_linear_map.to_sesq_form_apply_coe ContinuousLinearMap.toSesqForm_apply_coe

/- warning: continuous_linear_map.to_sesq_form_apply_norm_le -> ContinuousLinearMap.toSesqForm_apply_norm_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.to_sesq_form_apply_norm_le ContinuousLinearMap.toSesqForm_apply_norm_leₓ'. -/
theorem toSesqForm_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ‖toSesqForm f v‖ ≤ ‖f‖ * ‖v‖ :=
  by
  refine' op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  intro x
  have h₁ : ‖f x‖ ≤ ‖f‖ * ‖x‖ := le_op_norm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ _ v (f x)
  calc
    ‖⟪v, f x⟫‖ ≤ ‖v‖ * ‖f x‖ := h₂
    _ ≤ ‖v‖ * (‖f‖ * ‖x‖) := (mul_le_mul_of_nonneg_left h₁ (norm_nonneg v))
    _ = ‖f‖ * ‖v‖ * ‖x‖ := by ring
    
#align continuous_linear_map.to_sesq_form_apply_norm_le ContinuousLinearMap.toSesqForm_apply_norm_le

end ContinuousLinearMap

#print isBoundedBilinearMap_inner /-
/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `is_bounded_bilinear_map`.

In order to state these results, we need a `normed_space ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `inner_product_space.is_R_or_C_to_real 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[normed_space ℝ E]`.
-/
theorem isBoundedBilinearMap_inner [NormedSpace ℝ E] :
    IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := inner_add_left
    smul_left := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r x, algebra_map_eq_of_real, inner_smul_real_left]
    add_right := inner_add_right
    smul_right := fun r x y => by
      simp only [← algebraMap_smul 𝕜 r y, algebra_map_eq_of_real, inner_smul_real_right]
    bound := ⟨1, zero_lt_one, fun x y => by rw [one_mul]; exact norm_inner_le_norm x y⟩ }
#align is_bounded_bilinear_map_inner isBoundedBilinearMap_inner
-/

end Norm

section BesselsInequality

variable {ι : Type _} (x : E) {v : ι → E}

/- warning: orthonormal.sum_inner_products_le -> Orthonormal.sum_inner_products_le is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (x : E) {v : ι -> E} {s : Finset.{u3} ι}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (LE.le.{0} Real Real.hasLe (Finset.sum.{0, u3} Real ι Real.addCommMonoid s (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (x : E) {v : ι -> E} {s : Finset.{u3} ι}, (Orthonormal.{u2, u1, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (LE.le.{0} Real Real.instLEReal (Finset.sum.{0, u3} Real ι Real.instAddCommMonoidReal s (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u1} E (NormedAddCommGroup.toNorm.{u1} E _inst_2) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align orthonormal.sum_inner_products_le Orthonormal.sum_inner_products_leₓ'. -/
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
  rw [@norm_sub_sq 𝕜, sub_add]
  simp only [@InnerProductSpace.norm_sq_eq_inner 𝕜, inner_sum]
  simp only [sum_inner, two_mul, inner_smul_right, inner_conj_symm, ← mul_assoc, h₂, ← h₃,
    inner_conj_symm, AddMonoidHom.map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    inner_smul_left, add_sub_cancel']
#align orthonormal.sum_inner_products_le Orthonormal.sum_inner_products_le

/- warning: orthonormal.tsum_inner_products_le -> Orthonormal.tsum_inner_products_le is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (x : E) {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (LE.le.{0} Real Real.hasLe (tsum.{0, u3} Real Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ι (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u2} E (NormedAddCommGroup.toHasNorm.{u2} E _inst_2) x) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} (x : E) {v : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (LE.le.{0} Real Real.instLEReal (tsum.{0, u1} Real Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) ι (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u3} 𝕜 (NormedField.toNorm.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1))) (Inner.inner.{u3, u2} 𝕜 E (InnerProductSpace.toInner.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u2} E (NormedAddCommGroup.toNorm.{u2} E _inst_2) x) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align orthonormal.tsum_inner_products_le Orthonormal.tsum_inner_products_leₓ'. -/
/-- Bessel's inequality. -/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) :
    (∑' i, ‖⟪v i, x⟫‖ ^ 2) ≤ ‖x‖ ^ 2 :=
  by
  refine' tsum_le_of_sum_le' _ fun s => hv.sum_inner_products_le x
  simp only [norm_nonneg, pow_nonneg]
#align orthonormal.tsum_inner_products_le Orthonormal.tsum_inner_products_le

/- warning: orthonormal.inner_products_summable -> Orthonormal.inner_products_summable is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} (x : E) {v : ι -> E}, (Orthonormal.{u1, u2, u3} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (Summable.{0, u3} Real ι Real.addCommMonoid (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u1}} (x : E) {v : ι -> E}, (Orthonormal.{u3, u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι v) -> (Summable.{0, u1} Real ι Real.instAddCommMonoidReal (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (fun (i : ι) => HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u3} 𝕜 (NormedField.toNorm.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1))) (Inner.inner.{u3, u2} 𝕜 E (InnerProductSpace.toInner.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (v i) x)) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))))
Case conversion may be inaccurate. Consider using '#align orthonormal.inner_products_summable Orthonormal.inner_products_summableₓ'. -/
/-- The sum defined in Bessel's inequality is summable. -/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) :
    Summable fun i => ‖⟪v i, x⟫‖ ^ 2 :=
  by
  use ⨆ s : Finset ι, ∑ i in s, ‖⟪v i, x⟫‖ ^ 2
  apply hasSum_of_isLUB_of_nonneg
  · intro b
    simp only [norm_nonneg, pow_nonneg]
  · refine' isLUB_ciSup _
    use ‖x‖ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x
#align orthonormal.inner_products_summable Orthonormal.inner_products_summable

end BesselsInequality

#print IsROrC.innerProductSpace /-
/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance IsROrC.innerProductSpace : InnerProductSpace 𝕜 𝕜
    where
  inner x y := conj x * y
  norm_sq_eq_inner x := by unfold inner; rw [mul_comm, mul_conj, of_real_re, norm_sq_eq_def']
  conj_symm x y := by simp only [mul_comm, map_mul, starRingEnd_self_apply]
  add_left x y z := by simp only [add_mul, map_add]
  smul_left x y z := by simp only [mul_assoc, smul_eq_mul, map_mul]
#align is_R_or_C.inner_product_space IsROrC.innerProductSpace
-/

/- warning: is_R_or_C.inner_apply -> IsROrC.inner_apply is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] (x : 𝕜) (y : 𝕜), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u1} 𝕜 𝕜 (InnerProductSpace.toHasInner.{u1, u1} 𝕜 𝕜 _inst_1 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (IsROrC.innerProductSpace.{u1} 𝕜 _inst_1)) x y) (HMul.hMul.{u1, u1, u1} 𝕜 𝕜 𝕜 (instHMul.{u1} 𝕜 (Distrib.toHasMul.{u1} 𝕜 (Ring.toDistrib.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (coeFn.{succ u1, succ u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (_x : RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) => 𝕜 -> 𝕜) (RingHom.hasCoeToFun.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (starRingEnd.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u1} 𝕜 _inst_1)) x) y)
but is expected to have type
  forall {𝕜 : Type.{u1}} [_inst_1 : IsROrC.{u1} 𝕜] (x : 𝕜) (y : 𝕜), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u1} 𝕜 𝕜 (InnerProductSpace.toInner.{u1, u1} 𝕜 𝕜 _inst_1 (NonUnitalNormedRing.toNormedAddCommGroup.{u1} 𝕜 (NormedRing.toNonUnitalNormedRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (IsROrC.innerProductSpace.{u1} 𝕜 _inst_1)) x y) (HMul.hMul.{u1, u1, u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) 𝕜 ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (instHMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (NonUnitalNonAssocRing.toMul.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (NonAssocRing.toNonUnitalNonAssocRing.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (Ring.toNonAssocRing.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (NormedRing.toRing.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (NormedCommRing.toNormedRing.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (NormedField.toNormedCommRing.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (DenselyNormedField.toNormedField.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) (IsROrC.toDenselyNormedField.{u1} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) x) _inst_1))))))))) (FunLike.coe.{succ u1, succ u1, succ u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) 𝕜 (fun (_x : 𝕜) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : 𝕜) => 𝕜) _x) (MulHomClass.toFunLike.{u1, u1, u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonUnitalNonAssocSemiring.toMul.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (NonUnitalNonAssocSemiring.toMul.{u1} 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))) (NonUnitalRingHomClass.toMulHomClass.{u1, u1, u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) 𝕜 𝕜 (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (RingHomClass.toNonUnitalRingHomClass.{u1, u1, u1} (RingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (RingHom.instRingHomClassRingHom.{u1, u1} 𝕜 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (Semiring.toNonAssocSemiring.{u1} 𝕜 (CommSemiring.toSemiring.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))))))) (starRingEnd.{u1} 𝕜 (Semifield.toCommSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))) (IsROrC.toStarRing.{u1} 𝕜 _inst_1)) x) y)
Case conversion may be inaccurate. Consider using '#align is_R_or_C.inner_apply IsROrC.inner_applyₓ'. -/
@[simp]
theorem IsROrC.inner_apply (x y : 𝕜) : ⟪x, y⟫ = conj x * y :=
  rfl
#align is_R_or_C.inner_apply IsROrC.inner_apply

/-! ### Inner product space structure on subspaces -/


#print Submodule.innerProductSpace /-
/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  { Submodule.normedSpace W with
    inner := fun x y => ⟪(x : E), (y : E)⟫
    conj_symm := fun _ _ => inner_conj_symm _ _
    norm_sq_eq_inner := fun x => norm_sq_eq_inner (x : E)
    add_left := fun _ _ _ => inner_add_left _ _ _
    smul_left := fun _ _ _ => inner_smul_left _ _ _ }
#align submodule.inner_product_space Submodule.innerProductSpace
-/

/- warning: submodule.coe_inner -> Submodule.coe_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align submodule.coe_inner Submodule.coe_innerₓ'. -/
/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl
#align submodule.coe_inner Submodule.coe_inner

/- warning: orthonormal.cod_restrict -> Orthonormal.codRestrict is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.cod_restrict Orthonormal.codRestrictₓ'. -/
theorem Orthonormal.codRestrict {ι : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
    (hvs : ∀ i, v i ∈ s) : @Orthonormal 𝕜 s _ _ _ ι (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv
#align orthonormal.cod_restrict Orthonormal.codRestrict

/- warning: orthonormal_span -> orthonormal_span is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal_span orthonormal_spanₓ'. -/
theorem orthonormal_span {ι : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) :
    @Orthonormal 𝕜 (Submodule.span 𝕜 (Set.range v)) _ _ _ ι fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)
#align orthonormal_span orthonormal_span

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/


section OrthogonalFamily

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

open DirectSum

#print OrthogonalFamily /-
/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → submodule 𝕜 E`.  We
We instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.
The connection to the subobject spelling is shown in `orthogonal_family_iff_pairwise`.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`pi_lp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def OrthogonalFamily (G : ι → Type _) [∀ i, NormedAddCommGroup (G i)]
    [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0
#align orthogonal_family OrthogonalFamily
-/

variable {𝕜} {G : ι → Type _} [∀ i, NormedAddCommGroup (G i)] [∀ i, InnerProductSpace 𝕜 (G i)]
  {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 G V) [dec_V : ∀ (i) (x : G i), Decidable (x ≠ 0)]

/- warning: orthonormal.orthogonal_family -> Orthonormal.orthogonalFamily is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthonormal.orthogonal_family Orthonormal.orthogonalFamilyₓ'. -/
theorem Orthonormal.orthogonalFamily {v : ι → E} (hv : Orthonormal 𝕜 v) :
    OrthogonalFamily 𝕜 (fun i : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]
#align orthonormal.orthogonal_family Orthonormal.orthogonalFamily

include hV dec_ι

/- warning: orthogonal_family.eq_ite -> OrthogonalFamily.eq_ite is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.eq_ite OrthogonalFamily.eq_iteₓ'. -/
theorem OrthogonalFamily.eq_ite {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 :=
  by
  split_ifs
  · rfl
  · exact hV h v w
#align orthogonal_family.eq_ite OrthogonalFamily.eq_ite

include dec_V

/- warning: orthogonal_family.inner_right_dfinsupp -> OrthogonalFamily.inner_right_dfinsupp is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.inner_right_dfinsupp OrthogonalFamily.inner_right_dfinsuppₓ'. -/
theorem OrthogonalFamily.inner_right_dfinsupp (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.Sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.Sum fun j => V j⟫ = l.Sum fun j => fun w => ⟪V i v, V j w⟫ :=
      Dfinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.Sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.Sum <| funext fun j => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ :=
      by
      simp only [Dfinsupp.sum, Submodule.coe_inner, Finset.sum_ite_eq, ite_eq_left_iff,
        Dfinsupp.mem_support_toFun]
      split_ifs with h h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]
    
#align orthogonal_family.inner_right_dfinsupp OrthogonalFamily.inner_right_dfinsupp

omit dec_ι dec_V

/- warning: orthogonal_family.inner_right_fintype -> OrthogonalFamily.inner_right_fintype is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.inner_right_fintype OrthogonalFamily.inner_right_fintypeₓ'. -/
theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical calc
      ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
      _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
        (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
      _ = ⟪v, l i⟫ := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]
      
#align orthogonal_family.inner_right_fintype OrthogonalFamily.inner_right_fintype

/- warning: orthogonal_family.inner_sum -> OrthogonalFamily.inner_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.inner_sum OrthogonalFamily.inner_sumₓ'. -/
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

/- warning: orthogonal_family.norm_sum -> OrthogonalFamily.norm_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.norm_sum OrthogonalFamily.norm_sumₓ'. -/
theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) :
    ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2 :=
  by
  have : (‖∑ i in s, V i (l i)‖ ^ 2 : 𝕜) = ∑ i in s, ‖l i‖ ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact_mod_cast this
#align orthogonal_family.norm_sum OrthogonalFamily.norm_sum

/- warning: orthogonal_family.comp -> OrthogonalFamily.comp is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u3}} {G : ι -> Type.{u4}} [_inst_6 : forall (i : ι), NormedAddCommGroup.{u4} (G i)] [_inst_7 : forall (i : ι), InnerProductSpace.{u1, u4} 𝕜 (G i) _inst_1 (_inst_6 i)] {V : forall (i : ι), LinearIsometry.{u1, u1, u4, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (G i) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (G i) (_inst_6 i)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u1, u4} 𝕜 (G i) (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u4} (G i) (_inst_6 i)) (InnerProductSpace.toNormedSpace.{u1, u4} 𝕜 (G i) _inst_1 (_inst_6 i) (_inst_7 i))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))}, (OrthogonalFamily.{u1, u2, u3, u4} 𝕜 E _inst_1 _inst_2 _inst_3 ι G (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) V) -> (forall {γ : Type.{u5}} {f : γ -> ι}, (Function.Injective.{succ u5, succ u3} γ ι f) -> (OrthogonalFamily.{u1, u2, u5, u4} 𝕜 E _inst_1 _inst_2 _inst_3 γ (fun (g : γ) => G (f g)) (fun (i : γ) => _inst_6 (f i)) (fun (i : γ) => _inst_7 (f i)) (fun (g : γ) => V (f g))))
but is expected to have type
  forall {𝕜 : Type.{u3}} {E : Type.{u2}} [_inst_1 : IsROrC.{u3} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u3, u2} 𝕜 E _inst_1 _inst_2] {ι : Type.{u4}} {G : ι -> Type.{u1}} [_inst_6 : forall (i : ι), NormedAddCommGroup.{u1} (G i)] [_inst_7 : forall (i : ι), InnerProductSpace.{u3, u1} 𝕜 (G i) _inst_1 (_inst_6 i)] {V : forall (i : ι), LinearIsometry.{u3, u3, u1, u2} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))) (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))) (RingHom.id.{u3} 𝕜 (Semiring.toNonAssocSemiring.{u3} 𝕜 (DivisionSemiring.toSemiring.{u3} 𝕜 (Semifield.toDivisionSemiring.{u3} 𝕜 (Field.toSemifield.{u3} 𝕜 (NormedField.toField.{u3} 𝕜 (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)))))))) (G i) E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (G i) (_inst_6 i)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (NormedSpace.toModule.{u3, u1} 𝕜 (G i) (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} (G i) (_inst_6 i)) (InnerProductSpace.toNormedSpace.{u3, u1} 𝕜 (G i) _inst_1 (_inst_6 i) (_inst_7 i))) (NormedSpace.toModule.{u3, u2} 𝕜 E (DenselyNormedField.toNormedField.{u3} 𝕜 (IsROrC.toDenselyNormedField.{u3} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u3, u2} 𝕜 E _inst_1 _inst_2 _inst_3))}, (OrthogonalFamily.{u3, u2, u4, u1} 𝕜 E _inst_1 _inst_2 _inst_3 ι G (fun (i : ι) => _inst_6 i) (fun (i : ι) => _inst_7 i) V) -> (forall {γ : Type.{u5}} {f : γ -> ι}, (Function.Injective.{succ u5, succ u4} γ ι f) -> (OrthogonalFamily.{u3, u2, u5, u1} 𝕜 E _inst_1 _inst_2 _inst_3 γ (fun (g : γ) => G (f g)) (fun (i : γ) => _inst_6 (f i)) (fun (i : γ) => _inst_7 (f i)) (fun (g : γ) => V (f g))))
Case conversion may be inaccurate. Consider using '#align orthogonal_family.comp OrthogonalFamily.compₓ'. -/
/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp {γ : Type _} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f g) := fun i j hij v w => hV (hf.Ne hij) v w
#align orthogonal_family.comp OrthogonalFamily.comp

/- warning: orthogonal_family.orthonormal_sigma_orthonormal -> OrthogonalFamily.orthonormal_sigma_orthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.orthonormal_sigma_orthonormal OrthogonalFamily.orthonormal_sigma_orthonormalₓ'. -/
theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι → Type _} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σi, α i => V a.1 (v_family a.1 a.2) :=
  by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v ≠ w := fun h => by subst h; exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)
#align orthogonal_family.orthonormal_sigma_orthonormal OrthogonalFamily.orthonormal_sigma_orthonormal

include dec_ι

/- warning: orthogonal_family.norm_sq_diff_sum -> OrthogonalFamily.norm_sq_diff_sum is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.norm_sq_diff_sum OrthogonalFamily.norm_sq_diff_sumₓ'. -/
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

/- warning: orthogonal_family.summable_iff_norm_sq_summable -> OrthogonalFamily.summable_iff_norm_sq_summable is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.summable_iff_norm_sq_summable OrthogonalFamily.summable_iff_norm_sq_summableₓ'. -/
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
      refine' (abs_sub _ _).trans_lt _
      have : ∀ i, 0 ≤ ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i in s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2) < sqrt ε ^ 2 :=
        by
        rw [← hV.norm_sq_diff_sum, sq_lt_sq, abs_of_nonneg (sqrt_nonneg _),
          abs_of_nonneg (norm_nonneg _)]
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

/- warning: orthogonal_family.independent -> OrthogonalFamily.independent is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align orthogonal_family.independent OrthogonalFamily.independentₓ'. -/
/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem OrthogonalFamily.independent {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
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

/- warning: direct_sum.is_internal.collected_basis_orthonormal -> DirectSum.IsInternal.collectedBasis_orthonormal is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align direct_sum.is_internal.collected_basis_orthonormal DirectSum.IsInternal.collectedBasis_orthonormalₓ'. -/
theorem DirectSum.IsInternal.collectedBasis_orthonormal {V : ι → Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type _}
    {v_family : ∀ i, Basis (α i) 𝕜 (V i)} (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collected_basis_coe] using hV.orthonormal_sigma_orthonormal hv_family
#align direct_sum.is_internal.collected_basis_orthonormal DirectSum.IsInternal.collectedBasis_orthonormal

end OrthogonalFamily

section IsROrCToReal

variable {G : Type _}

variable (𝕜 E)

include 𝕜

#print Inner.isROrCToReal /-
/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def Inner.isROrCToReal : Inner ℝ E where inner x y := re ⟪x, y⟫
#align has_inner.is_R_or_C_to_real Inner.isROrCToReal
-/

#print InnerProductSpace.isROrCToReal /-
/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def InnerProductSpace.isROrCToReal : InnerProductSpace ℝ E :=
  { Inner.isROrCToReal 𝕜 E,
    NormedSpace.restrictScalars ℝ 𝕜
      E with
    norm_sq_eq_inner := norm_sq_eq_inner
    conj_symm := fun x y => inner_re_symm _ _
    add_left := fun x y z => by
      change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫
      simp only [inner_add_left, map_add]
    smul_left := fun x y r => by
      change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫
      simp only [inner_smul_left, conj_of_real, of_real_mul_re] }
#align inner_product_space.is_R_or_C_to_real InnerProductSpace.isROrCToReal
-/

variable {E}

/- warning: real_inner_eq_re_inner -> real_inner_eq_re_inner is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align real_inner_eq_re_inner real_inner_eq_re_innerₓ'. -/
theorem real_inner_eq_re_inner (x y : E) :
    @Inner.inner ℝ E (Inner.isROrCToReal 𝕜 E) x y = re ⟪x, y⟫ :=
  rfl
#align real_inner_eq_re_inner real_inner_eq_re_inner

/- warning: real_inner_I_smul_self -> real_inner_I_smul_self is a dubious translation:
lean 3 declaration is
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{1} Real (Inner.inner.{0, u2} Real E (Inner.isROrCToReal.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) (IsROrC.i.{u1} 𝕜 _inst_1) x)) (OfNat.ofNat.{0} Real 0 (OfNat.mk.{0} Real 0 (Zero.zero.{0} Real Real.hasZero)))
but is expected to have type
  forall (𝕜 : Type.{u1}) {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (x : E), Eq.{1} Real (Inner.inner.{0, u2} Real E (Inner.isROrCToReal.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) x (HSMul.hSMul.{u1, u2, u2} 𝕜 E E (instHSMul.{u1, u2} 𝕜 E (SMulZeroClass.toSMul.{u1, u2} 𝕜 E (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u1, u2} 𝕜 E (CommMonoidWithZero.toZero.{u1} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u1} 𝕜 (Semifield.toCommGroupWithZero.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u2} E (SubNegZeroMonoid.toNegZeroClass.{u2} E (SubtractionMonoid.toSubNegZeroMonoid.{u2} E (SubtractionCommMonoid.toSubtractionMonoid.{u2} E (AddCommGroup.toDivisionAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (DivisionSemiring.toSemiring.{u1} 𝕜 (Semifield.toDivisionSemiring.{u1} 𝕜 (Field.toSemifield.{u1} 𝕜 (NormedField.toField.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))))) (IsROrC.I.{u1} 𝕜 _inst_1) x)) (OfNat.ofNat.{0} Real 0 (Zero.toOfNat0.{0} Real Real.instZeroReal))
Case conversion may be inaccurate. Consider using '#align real_inner_I_smul_self real_inner_I_smul_selfₓ'. -/
theorem real_inner_I_smul_self (x : E) :
    @Inner.inner ℝ E (Inner.isROrCToReal 𝕜 E) x ((i : 𝕜) • x) = 0 := by
  simp [real_inner_eq_re_inner, inner_smul_right]
#align real_inner_I_smul_self real_inner_I_smul_self

omit 𝕜

/- warning: inner_product_space.complex_to_real -> InnerProductSpace.complexToReal is a dubious translation:
lean 3 declaration is
  forall {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : InnerProductSpace.{0, u1} Complex G Complex.isROrC _inst_6], InnerProductSpace.{0, u1} Real G Real.isROrC _inst_6
but is expected to have type
  forall {G : Type.{u1}} [_inst_6 : NormedAddCommGroup.{u1} G] [_inst_7 : InnerProductSpace.{0, u1} Complex G Complex.instIsROrCComplex _inst_6], InnerProductSpace.{0, u1} Real G Real.isROrC _inst_6
Case conversion may be inaccurate. Consider using '#align inner_product_space.complex_to_real InnerProductSpace.complexToRealₓ'. -/
/-- A complex inner product implies a real inner product -/
instance InnerProductSpace.complexToReal [NormedAddCommGroup G] [InnerProductSpace ℂ G] :
    InnerProductSpace ℝ G :=
  InnerProductSpace.isROrCToReal ℂ G
#align inner_product_space.complex_to_real InnerProductSpace.complexToReal

/- warning: complex.inner -> Complex.inner is a dubious translation:
lean 3 declaration is
  forall (w : Complex) (z : Complex), Eq.{1} Real (Inner.inner.{0, 0} Real Complex (InnerProductSpace.toHasInner.{0, 0} Real Complex Real.isROrC (NonUnitalNormedRing.toNormedAddCommGroup.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex (DenselyNormedField.toNormedField.{0} Complex (IsROrC.toDenselyNormedField.{0} Complex Complex.isROrC)))))) (InnerProductSpace.complexToReal.{0} Complex (NonUnitalNormedRing.toNormedAddCommGroup.{0} Complex (NormedRing.toNonUnitalNormedRing.{0} Complex (NormedCommRing.toNormedRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex (DenselyNormedField.toNormedField.{0} Complex (IsROrC.toDenselyNormedField.{0} Complex Complex.isROrC)))))) (IsROrC.innerProductSpace.{0} Complex Complex.isROrC))) w z) (Complex.re (HMul.hMul.{0, 0, 0} Complex Complex Complex (instHMul.{0} Complex Complex.hasMul) (coeFn.{1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (fun (_x : RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) => Complex -> Complex) (RingHom.hasCoeToFun.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.commSemiring))) (starRingEnd.{0} Complex Complex.commSemiring Complex.starRing) w) z))
but is expected to have type
  forall (w : Complex) (z : Complex), Eq.{1} Real (Inner.inner.{0, 0} Real Complex (InnerProductSpace.toInner.{0, 0} Real Complex Real.isROrC Complex.instNormedAddCommGroupComplex (InnerProductSpace.complexToReal.{0} Complex Complex.instNormedAddCommGroupComplex (IsROrC.innerProductSpace.{0} Complex Complex.instIsROrCComplex))) w z) (Complex.re (HMul.hMul.{0, 0, 0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) w) Complex ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) w) (instHMul.{0} ((fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) w) Complex.instMulComplex) (FunLike.coe.{1, 1, 1} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex (fun (_x : Complex) => (fun (x._@.Mathlib.Algebra.Hom.Group._hyg.2397 : Complex) => Complex) _x) (MulHomClass.toFunLike.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalNonAssocSemiring.toMul.{0} Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))) (NonUnitalRingHomClass.toMulHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (NonAssocSemiring.toNonUnitalNonAssocSemiring.{0} Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) (RingHomClass.toNonUnitalRingHomClass.{0, 0, 0} (RingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex))) Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (RingHom.instRingHomClassRingHom.{0, 0} Complex Complex (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)) (Semiring.toNonAssocSemiring.{0} Complex (CommSemiring.toSemiring.{0} Complex Complex.instCommSemiringComplex)))))) (starRingEnd.{0} Complex Complex.instCommSemiringComplex Complex.instStarRingComplexToNonUnitalSemiringToNonUnitalCommSemiringToNonUnitalCommRingCommRing) w) z))
Case conversion may be inaccurate. Consider using '#align complex.inner Complex.innerₓ'. -/
@[simp]
protected theorem Complex.inner (w z : ℂ) : ⟪w, z⟫_ℝ = (conj w * z).re :=
  rfl
#align complex.inner Complex.inner

/- warning: inner_map_complex -> inner_map_complex is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align inner_map_complex inner_map_complexₓ'. -/
/-- The inner product on an inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem inner_map_complex [NormedAddCommGroup G] [InnerProductSpace ℝ G] (f : G ≃ₗᵢ[ℝ] ℂ)
    (x y : G) : ⟪x, y⟫_ℝ = (conj (f x) * f y).re := by rw [← Complex.inner, f.inner_map_map]
#align inner_map_complex inner_map_complex

end IsROrCToReal

section Continuous

/-!
### Continuity of the inner product
-/


/- warning: continuous_inner -> continuous_inner is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} E E) 𝕜 (Prod.topologicalSpace.{u2, u2} E E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (p : Prod.{u2, u2} E E) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Prod.fst.{u2, u2} E E p) (Prod.snd.{u2, u2} E E p))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} E E) 𝕜 (instTopologicalSpaceProd.{u2, u2} E E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (p : Prod.{u2, u2} E E) => Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) (Prod.fst.{u2, u2} E E p) (Prod.snd.{u2, u2} E E p))
Case conversion may be inaccurate. Consider using '#align continuous_inner continuous_innerₓ'. -/
theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ :=
  letI : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  is_bounded_bilinear_map_inner.continuous
#align continuous_inner continuous_inner

variable {α : Type _}

#print Filter.Tendsto.inner /-
theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x))
    (hg : Tendsto g l (𝓝 y)) : Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.Tendsto _).comp (hf.prod_mk_nhds hg)
#align filter.tendsto.inner Filter.Tendsto.inner
-/

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

include 𝕜

#print ContinuousWithinAt.inner /-
theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  hf.inner hg
#align continuous_within_at.inner ContinuousWithinAt.inner
-/

#print ContinuousAt.inner /-
theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  hf.inner hg
#align continuous_at.inner ContinuousAt.inner
-/

#print ContinuousOn.inner /-
theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun t => ⟪f t, g t⟫) s := fun x hx => (hf x hx).inner (hg x hx)
#align continuous_on.inner ContinuousOn.inner
-/

#print Continuous.inner /-
@[continuity]
theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuousAt.2 fun x => hf.ContinuousAt.inner hg.ContinuousAt
#align continuous.inner Continuous.inner
-/

end Continuous

section ReApplyInnerSelf

#print ContinuousLinearMap.reApplyInnerSelf /-
/-- Extract a real bilinear form from an operator `T`, by taking the pairing `λ x, re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫
#align continuous_linear_map.re_apply_inner_self ContinuousLinearMap.reApplyInnerSelf
-/

/- warning: continuous_linear_map.re_apply_inner_self_apply -> ContinuousLinearMap.reApplyInnerSelf_apply is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.re_apply_inner_self_apply ContinuousLinearMap.reApplyInnerSelf_applyₓ'. -/
theorem ContinuousLinearMap.reApplyInnerSelf_apply (T : E →L[𝕜] E) (x : E) :
    T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl
#align continuous_linear_map.re_apply_inner_self_apply ContinuousLinearMap.reApplyInnerSelf_apply

/- warning: continuous_linear_map.re_apply_inner_self_continuous -> ContinuousLinearMap.reApplyInnerSelf_continuous is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (T : ContinuousLinearMap.{u1, u1, u2, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))), Continuous.{u2, 0} E Real (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ContinuousLinearMap.reApplyInnerSelf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (T : ContinuousLinearMap.{u2, u2, u1, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))), Continuous.{u1, 0} E Real (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (ContinuousLinearMap.reApplyInnerSelf.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T)
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.re_apply_inner_self_continuous ContinuousLinearMap.reApplyInnerSelf_continuousₓ'. -/
theorem ContinuousLinearMap.reApplyInnerSelf_continuous (T : E →L[𝕜] E) :
    Continuous T.reApplyInnerSelf :=
  reClm.Continuous.comp <| T.Continuous.inner continuous_id
#align continuous_linear_map.re_apply_inner_self_continuous ContinuousLinearMap.reApplyInnerSelf_continuous

/- warning: continuous_linear_map.re_apply_inner_self_smul -> ContinuousLinearMap.reApplyInnerSelf_smul is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (T : ContinuousLinearMap.{u1, u1, u2, u2} 𝕜 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (RingHom.id.{u1} 𝕜 (Semiring.toNonAssocSemiring.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) E (UniformSpace.toTopologicalSpace.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u2} E (NormedAddCommGroup.toAddCommGroup.{u2} E _inst_2)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))) (x : E) {c : 𝕜}, Eq.{1} Real (ContinuousLinearMap.reApplyInnerSelf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T (SMul.smul.{u1, u2} 𝕜 E (SMulZeroClass.toHasSmul.{u1, u2} 𝕜 E (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (SMulWithZero.toSmulZeroClass.{u1, u2} 𝕜 E (MulZeroClass.toHasZero.{u1} 𝕜 (MulZeroOneClass.toMulZeroClass.{u1} 𝕜 (MonoidWithZero.toMulZeroOneClass.{u1} 𝕜 (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u1, u2} 𝕜 E (Semiring.toMonoidWithZero.{u1} 𝕜 (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))))))) (AddZeroClass.toHasZero.{u2} E (AddMonoid.toAddZeroClass.{u2} E (AddCommMonoid.toAddMonoid.{u2} E (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (Module.toMulActionWithZero.{u1, u2} 𝕜 E (Ring.toSemiring.{u1} 𝕜 (NormedRing.toRing.{u1} 𝕜 (NormedCommRing.toNormedRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u2} E (SeminormedAddCommGroup.toAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (NormedSpace.toModule.{u1, u2} 𝕜 E (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2) (InnerProductSpace.toNormedSpace.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)))))) c x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.hasMul) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.monoid)) (Norm.norm.{u1} 𝕜 (NormedField.toHasNorm.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1))) c) (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne))))) (ContinuousLinearMap.reApplyInnerSelf.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3 T x))
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (T : ContinuousLinearMap.{u2, u2, u1, u1} 𝕜 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (RingHom.id.{u2} 𝕜 (Semiring.toNonAssocSemiring.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) E (UniformSpace.toTopologicalSpace.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))) (x : E) {c : 𝕜}, Eq.{1} Real (ContinuousLinearMap.reApplyInnerSelf.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T (HSMul.hSMul.{u2, u1, u1} 𝕜 E E (instHSMul.{u2, u1} 𝕜 E (SMulZeroClass.toSMul.{u2, u1} 𝕜 E (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (SMulWithZero.toSMulZeroClass.{u2, u1} 𝕜 E (CommMonoidWithZero.toZero.{u2} 𝕜 (CommGroupWithZero.toCommMonoidWithZero.{u2} 𝕜 (Semifield.toCommGroupWithZero.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (MulActionWithZero.toSMulWithZero.{u2, u1} 𝕜 E (Semiring.toMonoidWithZero.{u2} 𝕜 (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))))))) (NegZeroClass.toZero.{u1} E (SubNegZeroMonoid.toNegZeroClass.{u1} E (SubtractionMonoid.toSubNegZeroMonoid.{u1} E (SubtractionCommMonoid.toSubtractionMonoid.{u1} E (AddCommGroup.toDivisionAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)))))) (Module.toMulActionWithZero.{u2, u1} 𝕜 E (DivisionSemiring.toSemiring.{u2} 𝕜 (Semifield.toDivisionSemiring.{u2} 𝕜 (Field.toSemifield.{u2} 𝕜 (NormedField.toField.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))) (AddCommGroup.toAddCommMonoid.{u1} E (NormedAddCommGroup.toAddCommGroup.{u1} E _inst_2)) (NormedSpace.toModule.{u2, u1} 𝕜 E (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)) (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2) (InnerProductSpace.toNormedSpace.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3))))))) c x)) (HMul.hMul.{0, 0, 0} Real Real Real (instHMul.{0} Real Real.instMulReal) (HPow.hPow.{0, 0, 0} Real Nat Real (instHPow.{0, 0} Real Nat (Monoid.Pow.{0} Real Real.instMonoidReal)) (Norm.norm.{u2} 𝕜 (NormedField.toNorm.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1))) c) (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2))) (ContinuousLinearMap.reApplyInnerSelf.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3 T x))
Case conversion may be inaccurate. Consider using '#align continuous_linear_map.re_apply_inner_self_smul ContinuousLinearMap.reApplyInnerSelf_smulₓ'. -/
theorem ContinuousLinearMap.reApplyInnerSelf_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ‖c‖ ^ 2 * T.reApplyInnerSelf x := by
  simp only [ContinuousLinearMap.map_smul, ContinuousLinearMap.reApplyInnerSelf_apply,
    inner_smul_left, inner_smul_right, ← mul_assoc, mul_conj, norm_sq_eq_def', ← smul_re,
    Algebra.smul_def (‖c‖ ^ 2) ⟪T x, x⟫, algebra_map_eq_of_real]
#align continuous_linear_map.re_apply_inner_self_smul ContinuousLinearMap.reApplyInnerSelf_smul

end ReApplyInnerSelf

namespace UniformSpace.Completion

open UniformSpace Function

instance {𝕜' E' : Type _} [TopologicalSpace 𝕜'] [UniformSpace E'] [Inner 𝕜' E'] :
    Inner 𝕜' (Completion E')
    where inner := curry <| (denseInducing_coe.Prod denseInducing_coe).extend (uncurry inner)

/- warning: uniform_space.completion.inner_coe -> UniformSpace.Completion.inner_coe is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] (a : E) (b : E), Eq.{succ u1} 𝕜 (Inner.inner.{u1, u2} 𝕜 (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.hasInner.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (HasLiftT.mk.{succ u2, succ u2} E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (CoeTCₓ.coe.{succ u2, succ u2} E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.hasCoeT.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) a) ((fun (a : Type.{u2}) (b : Type.{u2}) [self : HasLiftT.{succ u2, succ u2} a b] => self.0) E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (HasLiftT.mk.{succ u2, succ u2} E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (CoeTCₓ.coe.{succ u2, succ u2} E (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.hasCoeT.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) b)) (Inner.inner.{u1, u2} 𝕜 E (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3) a b)
but is expected to have type
  forall {𝕜 : Type.{u2}} {E : Type.{u1}} [_inst_1 : IsROrC.{u2} 𝕜] [_inst_2 : NormedAddCommGroup.{u1} E] [_inst_3 : InnerProductSpace.{u2, u1} 𝕜 E _inst_1 _inst_2] (a : E) (b : E), Eq.{succ u2} 𝕜 (Inner.inner.{u2, u1} 𝕜 (UniformSpace.Completion.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2)))) (UniformSpace.Completion.toInner.{u2, u1} 𝕜 E (UniformSpace.toTopologicalSpace.{u2} 𝕜 (PseudoMetricSpace.toUniformSpace.{u2} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u2} 𝕜 (SeminormedCommRing.toSeminormedRing.{u2} 𝕜 (NormedCommRing.toSeminormedCommRing.{u2} 𝕜 (NormedField.toNormedCommRing.{u2} 𝕜 (DenselyNormedField.toNormedField.{u2} 𝕜 (IsROrC.toDenselyNormedField.{u2} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3)) (UniformSpace.Completion.coe'.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) a) (UniformSpace.Completion.coe'.{u1} E (PseudoMetricSpace.toUniformSpace.{u1} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u1} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u1} E _inst_2))) b)) (Inner.inner.{u2, u1} 𝕜 E (InnerProductSpace.toInner.{u2, u1} 𝕜 E _inst_1 _inst_2 _inst_3) a b)
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.inner_coe UniformSpace.Completion.inner_coeₓ'. -/
@[simp]
theorem inner_coe (a b : E) : inner (a : Completion E) (b : Completion E) = (inner a b : 𝕜) :=
  (denseInducing_coe.Prod denseInducing_coe).extend_eq
    (continuous_inner : Continuous (uncurry inner : E × E → 𝕜)) (a, b)
#align uniform_space.completion.inner_coe UniformSpace.Completion.inner_coe

/- warning: uniform_space.completion.continuous_inner -> UniformSpace.Completion.continuous_inner is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) 𝕜 (Prod.topologicalSpace.{u2, u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Function.uncurry.{u2, u2, u1} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) 𝕜 (Inner.inner.{u1, u2} 𝕜 (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.hasInner.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2], Continuous.{u2, u1} (Prod.{u2, u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))) 𝕜 (instTopologicalSpaceProd.{u2, u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))))) (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (Function.uncurry.{u2, u2, u1} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) 𝕜 (Inner.inner.{u1, u2} 𝕜 (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.toInner.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3))))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.continuous_inner UniformSpace.Completion.continuous_innerₓ'. -/
protected theorem continuous_inner : Continuous (uncurry inner : Completion E × Completion E → 𝕜) :=
  by
  let inner' : E →+ E →+ 𝕜 :=
    { toFun := fun x => (innerₛₗ 𝕜 x).toAddMonoidHom
      map_zero' := by ext x <;> exact inner_zero_left _
      map_add' := fun x y => by ext z <;> exact inner_add_left _ _ _ }
  have : Continuous fun p : E × E => inner' p.1 p.2 := continuous_inner
  rw [completion.has_inner, uncurry_curry _]
  change
    Continuous
      (((dense_inducing_to_compl E).Prod (dense_inducing_to_compl E)).extend fun p : E × E =>
        inner' p.1 p.2)
  exact (dense_inducing_to_compl E).extend_Z_bilin (dense_inducing_to_compl E) this
#align uniform_space.completion.continuous_inner UniformSpace.Completion.continuous_inner

/- warning: uniform_space.completion.continuous.inner -> UniformSpace.Completion.Continuous.inner is a dubious translation:
lean 3 declaration is
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {α : Type.{u3}} [_inst_6 : TopologicalSpace.{u3} α] {f : α -> (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))} {g : α -> (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))}, (Continuous.{u3, u2} α (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_6 (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) f) -> (Continuous.{u3, u2} α (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_6 (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.normedAddCommGroup.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) g) -> (Continuous.{u3, u1} α 𝕜 _inst_6 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (x : α) => Inner.inner.{u1, u2} 𝕜 (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.hasInner.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSemiNormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (InnerProductSpace.toHasInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (f x) (g x)))
but is expected to have type
  forall {𝕜 : Type.{u1}} {E : Type.{u2}} [_inst_1 : IsROrC.{u1} 𝕜] [_inst_2 : NormedAddCommGroup.{u2} E] [_inst_3 : InnerProductSpace.{u1, u2} 𝕜 E _inst_1 _inst_2] {α : Type.{u3}} [_inst_6 : TopologicalSpace.{u3} α] {f : α -> (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))} {g : α -> (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))))}, (Continuous.{u3, u2} α (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_6 (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) f) -> (Continuous.{u3, u2} α (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) _inst_6 (UniformSpace.toTopologicalSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (PseudoMetricSpace.toUniformSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.instNormedAddCommGroupCompletionToUniformSpaceToPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))))) g) -> (Continuous.{u3, u1} α 𝕜 _inst_6 (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (fun (x : α) => Inner.inner.{u1, u2} 𝕜 (UniformSpace.Completion.{u2} E (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2)))) (UniformSpace.Completion.toInner.{u1, u2} 𝕜 E (UniformSpace.toTopologicalSpace.{u1} 𝕜 (PseudoMetricSpace.toUniformSpace.{u1} 𝕜 (SeminormedRing.toPseudoMetricSpace.{u1} 𝕜 (SeminormedCommRing.toSeminormedRing.{u1} 𝕜 (NormedCommRing.toSeminormedCommRing.{u1} 𝕜 (NormedField.toNormedCommRing.{u1} 𝕜 (DenselyNormedField.toNormedField.{u1} 𝕜 (IsROrC.toDenselyNormedField.{u1} 𝕜 _inst_1)))))))) (PseudoMetricSpace.toUniformSpace.{u2} E (SeminormedAddCommGroup.toPseudoMetricSpace.{u2} E (NormedAddCommGroup.toSeminormedAddCommGroup.{u2} E _inst_2))) (InnerProductSpace.toInner.{u1, u2} 𝕜 E _inst_1 _inst_2 _inst_3)) (f x) (g x)))
Case conversion may be inaccurate. Consider using '#align uniform_space.completion.continuous.inner UniformSpace.Completion.Continuous.innerₓ'. -/
protected theorem Continuous.inner {α : Type _} [TopologicalSpace α] {f g : α → Completion E}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x : α => inner (f x) (g x) : α → 𝕜) :=
  UniformSpace.Completion.continuous_inner.comp (hf.prod_mk hg : _)
#align uniform_space.completion.continuous.inner UniformSpace.Completion.Continuous.inner

instance : InnerProductSpace 𝕜 (Completion E)
    where
  norm_sq_eq_inner x :=
    Completion.induction_on x
      (isClosed_eq (continuous_norm.pow 2)
        (continuous_re.comp (Continuous.inner continuous_id' continuous_id')))
      fun a => by simp only [norm_coe, inner_coe, inner_self_eq_norm_sq]
  conj_symm x y :=
    Completion.induction_on₂ x y
      (isClosed_eq (continuous_conj.comp (Continuous.inner continuous_snd continuous_fst))
        (Continuous.inner continuous_fst continuous_snd))
      fun a b => by simp only [inner_coe, inner_conj_symm]
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

