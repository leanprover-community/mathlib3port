/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.complex.re_im_topology
! leanprover-community/mathlib commit 2ed2c6310e6f1c5562bdf6bfbda55ebbf6891abe
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this fact we use the fact that `ℂ` is naturally homeomorphic to `ℝ × ℝ` to deduce some
topological properties of `complex.re` and `complex.im`.

## Main statements

Each statement about `complex.re` listed below has a counterpart about `complex.im`.

* `complex.is_homeomorphic_trivial_fiber_bundle_re`: `complex.re` turns `ℂ` into a trivial
  topological fiber bundle over `ℝ`;
* `complex.is_open_map_re`, `complex.quotient_map_re`: in particular, `complex.re` is an open map
  and is a quotient map;
* `complex.interior_preimage_re`, `complex.closure_preimage_re`, `complex.frontier_preimage_re`:
  formulas for `interior (complex.re ⁻¹' s)` etc;
* `complex.interior_set_of_re_le` etc: particular cases of the above formulas in the cases when `s`
  is one of the infinite intervals `set.Ioi a`, `set.Ici a`, `set.Iio a`, and `set.Iic a`,
  formulated as `interior {z : ℂ | z.re ≤ a} = {z | z.re < a}` etc.

## Tags

complex, real part, imaginary part, closure, interior, frontier
-/


open Set

noncomputable section

namespace Complex

/- warning: complex.is_homeomorphic_trivial_fiber_bundle_re -> Complex.isHomeomorphicTrivialFiberBundle_re is a dubious translation:
lean 3 declaration is
  IsHomeomorphicTrivialFiberBundle.{0, 0, 0} Real Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.re
but is expected to have type
  IsHomeomorphicTrivialFiberBundle.{0, 0, 0} Real Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.re
Case conversion may be inaccurate. Consider using '#align complex.is_homeomorphic_trivial_fiber_bundle_re Complex.isHomeomorphicTrivialFiberBundle_reₓ'. -/
/-- `complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem isHomeomorphicTrivialFiberBundle_re : IsHomeomorphicTrivialFiberBundle ℝ re :=
  ⟨equivRealProdClm.toHomeomorph, fun z => rfl⟩
#align complex.is_homeomorphic_trivial_fiber_bundle_re Complex.isHomeomorphicTrivialFiberBundle_re

/- warning: complex.is_homeomorphic_trivial_fiber_bundle_im -> Complex.isHomeomorphicTrivialFiberBundle_im is a dubious translation:
lean 3 declaration is
  IsHomeomorphicTrivialFiberBundle.{0, 0, 0} Real Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) Complex.im
but is expected to have type
  IsHomeomorphicTrivialFiberBundle.{0, 0, 0} Real Real Complex (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) Complex.im
Case conversion may be inaccurate. Consider using '#align complex.is_homeomorphic_trivial_fiber_bundle_im Complex.isHomeomorphicTrivialFiberBundle_imₓ'. -/
/-- `complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem isHomeomorphicTrivialFiberBundle_im : IsHomeomorphicTrivialFiberBundle ℝ im :=
  ⟨equivRealProdClm.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ), fun z => rfl⟩
#align complex.is_homeomorphic_trivial_fiber_bundle_im Complex.isHomeomorphicTrivialFiberBundle_im

/- warning: complex.is_open_map_re -> Complex.isOpenMap_re is a dubious translation:
lean 3 declaration is
  IsOpenMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.re
but is expected to have type
  IsOpenMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.re
Case conversion may be inaccurate. Consider using '#align complex.is_open_map_re Complex.isOpenMap_reₓ'. -/
theorem isOpenMap_re : IsOpenMap re :=
  isHomeomorphicTrivialFiberBundle_re.isOpenMap_proj
#align complex.is_open_map_re Complex.isOpenMap_re

/- warning: complex.is_open_map_im -> Complex.isOpenMap_im is a dubious translation:
lean 3 declaration is
  IsOpenMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.im
but is expected to have type
  IsOpenMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.im
Case conversion may be inaccurate. Consider using '#align complex.is_open_map_im Complex.isOpenMap_imₓ'. -/
theorem isOpenMap_im : IsOpenMap im :=
  isHomeomorphicTrivialFiberBundle_im.isOpenMap_proj
#align complex.is_open_map_im Complex.isOpenMap_im

/- warning: complex.quotient_map_re -> Complex.quotientMap_re is a dubious translation:
lean 3 declaration is
  QuotientMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.re
but is expected to have type
  QuotientMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.re
Case conversion may be inaccurate. Consider using '#align complex.quotient_map_re Complex.quotientMap_reₓ'. -/
theorem quotientMap_re : QuotientMap re :=
  isHomeomorphicTrivialFiberBundle_re.quotientMap_proj
#align complex.quotient_map_re Complex.quotientMap_re

/- warning: complex.quotient_map_im -> Complex.quotientMap_im is a dubious translation:
lean 3 declaration is
  QuotientMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.im
but is expected to have type
  QuotientMap.{0, 0} Complex Real (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) Complex.im
Case conversion may be inaccurate. Consider using '#align complex.quotient_map_im Complex.quotientMap_imₓ'. -/
theorem quotientMap_im : QuotientMap im :=
  isHomeomorphicTrivialFiberBundle_im.quotientMap_proj
#align complex.quotient_map_im Complex.quotientMap_im

/- warning: complex.interior_preimage_re -> Complex.interior_preimage_re is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.interior_preimage_re Complex.interior_preimage_reₓ'. -/
theorem interior_preimage_re (s : Set ℝ) : interior (re ⁻¹' s) = re ⁻¹' interior s :=
  (isOpenMap_re.preimage_interior_eq_interior_preimage continuous_re _).symm
#align complex.interior_preimage_re Complex.interior_preimage_re

/- warning: complex.interior_preimage_im -> Complex.interior_preimage_im is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.interior_preimage_im Complex.interior_preimage_imₓ'. -/
theorem interior_preimage_im (s : Set ℝ) : interior (im ⁻¹' s) = im ⁻¹' interior s :=
  (isOpenMap_im.preimage_interior_eq_interior_preimage continuous_im _).symm
#align complex.interior_preimage_im Complex.interior_preimage_im

/- warning: complex.closure_preimage_re -> Complex.closure_preimage_re is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.closure_preimage_re Complex.closure_preimage_reₓ'. -/
theorem closure_preimage_re (s : Set ℝ) : closure (re ⁻¹' s) = re ⁻¹' closure s :=
  (isOpenMap_re.preimage_closure_eq_closure_preimage continuous_re _).symm
#align complex.closure_preimage_re Complex.closure_preimage_re

/- warning: complex.closure_preimage_im -> Complex.closure_preimage_im is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.closure_preimage_im Complex.closure_preimage_imₓ'. -/
theorem closure_preimage_im (s : Set ℝ) : closure (im ⁻¹' s) = im ⁻¹' closure s :=
  (isOpenMap_im.preimage_closure_eq_closure_preimage continuous_im _).symm
#align complex.closure_preimage_im Complex.closure_preimage_im

/- warning: complex.frontier_preimage_re -> Complex.frontier_preimage_re is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.re s)) (Set.preimage.{0, 0} Complex Real Complex.re (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.frontier_preimage_re Complex.frontier_preimage_reₓ'. -/
theorem frontier_preimage_re (s : Set ℝ) : frontier (re ⁻¹' s) = re ⁻¹' frontier s :=
  (isOpenMap_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm
#align complex.frontier_preimage_re Complex.frontier_preimage_re

/- warning: complex.frontier_preimage_im -> Complex.frontier_preimage_im is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
but is expected to have type
  forall (s : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Set.preimage.{0, 0} Complex Real Complex.im s)) (Set.preimage.{0, 0} Complex Real Complex.im (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s))
Case conversion may be inaccurate. Consider using '#align complex.frontier_preimage_im Complex.frontier_preimage_imₓ'. -/
theorem frontier_preimage_im (s : Set ℝ) : frontier (im ⁻¹' s) = im ⁻¹' frontier s :=
  (isOpenMap_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm
#align complex.frontier_preimage_im Complex.frontier_preimage_im

/- warning: complex.interior_set_of_re_le -> Complex.interior_setOf_re_le is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.interior_set_of_re_le Complex.interior_setOf_re_leₓ'. -/
@[simp]
theorem interior_setOf_re_le (a : ℝ) : interior { z : ℂ | z.re ≤ a } = { z | z.re < a } := by
  simpa only [interior_Iic] using interior_preimage_re (Iic a)
#align complex.interior_set_of_re_le Complex.interior_setOf_re_le

/- warning: complex.interior_set_of_im_le -> Complex.interior_setOf_im_le is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.interior_set_of_im_le Complex.interior_setOf_im_leₓ'. -/
@[simp]
theorem interior_setOf_im_le (a : ℝ) : interior { z : ℂ | z.im ≤ a } = { z | z.im < a } := by
  simpa only [interior_Iic] using interior_preimage_im (Iic a)
#align complex.interior_set_of_im_le Complex.interior_setOf_im_le

/- warning: complex.interior_set_of_le_re -> Complex.interior_setOf_le_re is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.re z)))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.re z)))
Case conversion may be inaccurate. Consider using '#align complex.interior_set_of_le_re Complex.interior_setOf_le_reₓ'. -/
@[simp]
theorem interior_setOf_le_re (a : ℝ) : interior { z : ℂ | a ≤ z.re } = { z | a < z.re } := by
  simpa only [interior_Ici] using interior_preimage_re (Ici a)
#align complex.interior_set_of_le_re Complex.interior_setOf_le_re

/- warning: complex.interior_set_of_le_im -> Complex.interior_setOf_le_im is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.im z)))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.im z)))
Case conversion may be inaccurate. Consider using '#align complex.interior_set_of_le_im Complex.interior_setOf_le_imₓ'. -/
@[simp]
theorem interior_setOf_le_im (a : ℝ) : interior { z : ℂ | a ≤ z.im } = { z | a < z.im } := by
  simpa only [interior_Ici] using interior_preimage_im (Ici a)
#align complex.interior_set_of_le_im Complex.interior_setOf_le_im

/- warning: complex.closure_set_of_re_lt -> Complex.closure_setOf_re_lt is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.closure_set_of_re_lt Complex.closure_setOf_re_ltₓ'. -/
@[simp]
theorem closure_setOf_re_lt (a : ℝ) : closure { z : ℂ | z.re < a } = { z | z.re ≤ a } := by
  simpa only [closure_Iio] using closure_preimage_re (Iio a)
#align complex.closure_set_of_re_lt Complex.closure_setOf_re_lt

/- warning: complex.closure_set_of_im_lt -> Complex.closure_setOf_im_lt is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.closure_set_of_im_lt Complex.closure_setOf_im_ltₓ'. -/
@[simp]
theorem closure_setOf_im_lt (a : ℝ) : closure { z : ℂ | z.im < a } = { z | z.im ≤ a } := by
  simpa only [closure_Iio] using closure_preimage_im (Iio a)
#align complex.closure_set_of_im_lt Complex.closure_setOf_im_lt

/- warning: complex.closure_set_of_lt_re -> Complex.closure_setOf_lt_re is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.re z)))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.re z)))
Case conversion may be inaccurate. Consider using '#align complex.closure_set_of_lt_re Complex.closure_setOf_lt_reₓ'. -/
@[simp]
theorem closure_setOf_lt_re (a : ℝ) : closure { z : ℂ | a < z.re } = { z | a ≤ z.re } := by
  simpa only [closure_Ioi] using closure_preimage_re (Ioi a)
#align complex.closure_set_of_lt_re Complex.closure_setOf_lt_re

/- warning: complex.closure_set_of_lt_im -> Complex.closure_setOf_lt_im is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.im z)))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.im z)))
Case conversion may be inaccurate. Consider using '#align complex.closure_set_of_lt_im Complex.closure_setOf_lt_imₓ'. -/
@[simp]
theorem closure_setOf_lt_im (a : ℝ) : closure { z : ℂ | a < z.im } = { z | a ≤ z.im } := by
  simpa only [closure_Ioi] using closure_preimage_im (Ioi a)
#align complex.closure_set_of_lt_im Complex.closure_setOf_lt_im

/- warning: complex.frontier_set_of_re_le -> Complex.frontier_setOf_re_le is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_re_le Complex.frontier_setOf_re_leₓ'. -/
@[simp]
theorem frontier_setOf_re_le (a : ℝ) : frontier { z : ℂ | z.re ≤ a } = { z | z.re = a } := by
  simpa only [frontier_Iic] using frontier_preimage_re (Iic a)
#align complex.frontier_set_of_re_le Complex.frontier_setOf_re_le

/- warning: complex.frontier_set_of_im_le -> Complex.frontier_setOf_im_le is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_im_le Complex.frontier_setOf_im_leₓ'. -/
@[simp]
theorem frontier_setOf_im_le (a : ℝ) : frontier { z : ℂ | z.im ≤ a } = { z | z.im = a } := by
  simpa only [frontier_Iic] using frontier_preimage_im (Iic a)
#align complex.frontier_set_of_im_le Complex.frontier_setOf_im_le

/- warning: complex.frontier_set_of_le_re -> Complex.frontier_setOf_le_re is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_le_re Complex.frontier_setOf_le_reₓ'. -/
@[simp]
theorem frontier_setOf_le_re (a : ℝ) : frontier { z : ℂ | a ≤ z.re } = { z | z.re = a } := by
  simpa only [frontier_Ici] using frontier_preimage_re (Ici a)
#align complex.frontier_set_of_le_re Complex.frontier_setOf_le_re

/- warning: complex.frontier_set_of_le_im -> Complex.frontier_setOf_le_im is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.hasLe a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LE.le.{0} Real Real.instLEReal a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_le_im Complex.frontier_setOf_le_imₓ'. -/
@[simp]
theorem frontier_setOf_le_im (a : ℝ) : frontier { z : ℂ | a ≤ z.im } = { z | z.im = a } := by
  simpa only [frontier_Ici] using frontier_preimage_im (Ici a)
#align complex.frontier_set_of_le_im Complex.frontier_setOf_le_im

/- warning: complex.frontier_set_of_re_lt -> Complex.frontier_setOf_re_lt is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.re z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_re_lt Complex.frontier_setOf_re_ltₓ'. -/
@[simp]
theorem frontier_setOf_re_lt (a : ℝ) : frontier { z : ℂ | z.re < a } = { z | z.re = a } := by
  simpa only [frontier_Iio] using frontier_preimage_re (Iio a)
#align complex.frontier_set_of_re_lt Complex.frontier_setOf_re_lt

/- warning: complex.frontier_set_of_im_lt -> Complex.frontier_setOf_im_lt is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal (Complex.im z) a))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_im_lt Complex.frontier_setOf_im_ltₓ'. -/
@[simp]
theorem frontier_setOf_im_lt (a : ℝ) : frontier { z : ℂ | z.im < a } = { z | z.im = a } := by
  simpa only [frontier_Iio] using frontier_preimage_im (Iio a)
#align complex.frontier_set_of_im_lt Complex.frontier_setOf_im_lt

/- warning: complex.frontier_set_of_lt_re -> Complex.frontier_setOf_lt_re is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.re z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.re z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_lt_re Complex.frontier_setOf_lt_reₓ'. -/
@[simp]
theorem frontier_setOf_lt_re (a : ℝ) : frontier { z : ℂ | a < z.re } = { z | z.re = a } := by
  simpa only [frontier_Ioi] using frontier_preimage_re (Ioi a)
#align complex.frontier_set_of_lt_re Complex.frontier_setOf_lt_re

/- warning: complex.frontier_set_of_lt_im -> Complex.frontier_setOf_lt_im is a dubious translation:
lean 3 declaration is
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.hasLt a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
but is expected to have type
  forall (a : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => LT.lt.{0} Real Real.instLTReal a (Complex.im z)))) (setOf.{0} Complex (fun (z : Complex) => Eq.{1} Real (Complex.im z) a))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_lt_im Complex.frontier_setOf_lt_imₓ'. -/
@[simp]
theorem frontier_setOf_lt_im (a : ℝ) : frontier { z : ℂ | a < z.im } = { z | z.im = a } := by
  simpa only [frontier_Ioi] using frontier_preimage_im (Ioi a)
#align complex.frontier_set_of_lt_im Complex.frontier_setOf_lt_im

/- warning: complex.closure_re_prod_im -> Complex.closure_reProdIm is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.Set.reProdIm s t)) (Complex.Set.reProdIm (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t))
but is expected to have type
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (closure.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.Set.reProdIm s t)) (Complex.Set.reProdIm (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t))
Case conversion may be inaccurate. Consider using '#align complex.closure_re_prod_im Complex.closure_reProdImₓ'. -/
theorem closure_reProdIm (s t : Set ℝ) : closure (s ×ℂ t) = closure s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equiv_real_prod_clm.symm.to_homeomorph.surjective,
    equiv_real_prod_clm.symm.to_homeomorph.preimage_closure] using @closure_prod_eq _ _ _ _ s t
#align complex.closure_re_prod_im Complex.closure_reProdIm

/- warning: complex.interior_re_prod_im -> Complex.interior_reProdIm is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.Set.reProdIm s t)) (Complex.Set.reProdIm (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t))
but is expected to have type
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (interior.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.Set.reProdIm s t)) (Complex.Set.reProdIm (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (interior.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t))
Case conversion may be inaccurate. Consider using '#align complex.interior_re_prod_im Complex.interior_reProdImₓ'. -/
theorem interior_reProdIm (s t : Set ℝ) : interior (s ×ℂ t) = interior s ×ℂ interior t := by
  rw [re_prod_im, re_prod_im, interior_inter, interior_preimage_re, interior_preimage_im]
#align complex.interior_re_prod_im Complex.interior_reProdIm

/- warning: complex.frontier_re_prod_im -> Complex.frontier_reProdIm is a dubious translation:
lean 3 declaration is
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.Set.reProdIm s t)) (Union.union.{0} (Set.{0} Complex) (Set.hasUnion.{0} Complex) (Complex.Set.reProdIm (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t)) (Complex.Set.reProdIm (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t)))
but is expected to have type
  forall (s : Set.{0} Real) (t : Set.{0} Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.Set.reProdIm s t)) (Union.union.{0} (Set.{0} Complex) (Set.instUnionSet.{0} Complex) (Complex.Set.reProdIm (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t)) (Complex.Set.reProdIm (frontier.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) (closure.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t)))
Case conversion may be inaccurate. Consider using '#align complex.frontier_re_prod_im Complex.frontier_reProdImₓ'. -/
theorem frontier_reProdIm (s t : Set ℝ) :
    frontier (s ×ℂ t) = closure s ×ℂ frontier t ∪ frontier s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equiv_real_prod_clm.symm.to_homeomorph.surjective,
    equiv_real_prod_clm.symm.to_homeomorph.preimage_frontier] using frontier_prod_eq s t
#align complex.frontier_re_prod_im Complex.frontier_reProdIm

/- warning: complex.frontier_set_of_le_re_and_le_im -> Complex.frontier_setOf_le_re_and_le_im is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => And (LE.le.{0} Real Real.hasLe a (Complex.re z)) (LE.le.{0} Real Real.hasLe b (Complex.im z))))) (setOf.{0} Complex (fun (z : Complex) => Or (And (LE.le.{0} Real Real.hasLe a (Complex.re z)) (Eq.{1} Real (Complex.im z) b)) (And (Eq.{1} Real (Complex.re z) a) (LE.le.{0} Real Real.hasLe b (Complex.im z)))))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => And (LE.le.{0} Real Real.instLEReal a (Complex.re z)) (LE.le.{0} Real Real.instLEReal b (Complex.im z))))) (setOf.{0} Complex (fun (z : Complex) => Or (And (LE.le.{0} Real Real.instLEReal a (Complex.re z)) (Eq.{1} Real (Complex.im z) b)) (And (Eq.{1} Real (Complex.re z) a) (LE.le.{0} Real Real.instLEReal b (Complex.im z)))))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_le_re_and_le_im Complex.frontier_setOf_le_re_and_le_imₓ'. -/
theorem frontier_setOf_le_re_and_le_im (a b : ℝ) :
    frontier { z | a ≤ re z ∧ b ≤ im z } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ b ≤ im z } := by
  simpa only [closure_Ici, frontier_Ici] using frontier_re_prod_im (Ici a) (Ici b)
#align complex.frontier_set_of_le_re_and_le_im Complex.frontier_setOf_le_re_and_le_im

/- warning: complex.frontier_set_of_le_re_and_im_le -> Complex.frontier_setOf_le_re_and_im_le is a dubious translation:
lean 3 declaration is
  forall (a : Real) (b : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (setOf.{0} Complex (fun (z : Complex) => And (LE.le.{0} Real Real.hasLe a (Complex.re z)) (LE.le.{0} Real Real.hasLe (Complex.im z) b)))) (setOf.{0} Complex (fun (z : Complex) => Or (And (LE.le.{0} Real Real.hasLe a (Complex.re z)) (Eq.{1} Real (Complex.im z) b)) (And (Eq.{1} Real (Complex.re z) a) (LE.le.{0} Real Real.hasLe (Complex.im z) b))))
but is expected to have type
  forall (a : Real) (b : Real), Eq.{1} (Set.{0} Complex) (frontier.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (setOf.{0} Complex (fun (z : Complex) => And (LE.le.{0} Real Real.instLEReal a (Complex.re z)) (LE.le.{0} Real Real.instLEReal (Complex.im z) b)))) (setOf.{0} Complex (fun (z : Complex) => Or (And (LE.le.{0} Real Real.instLEReal a (Complex.re z)) (Eq.{1} Real (Complex.im z) b)) (And (Eq.{1} Real (Complex.re z) a) (LE.le.{0} Real Real.instLEReal (Complex.im z) b))))
Case conversion may be inaccurate. Consider using '#align complex.frontier_set_of_le_re_and_im_le Complex.frontier_setOf_le_re_and_im_leₓ'. -/
theorem frontier_setOf_le_re_and_im_le (a b : ℝ) :
    frontier { z | a ≤ re z ∧ im z ≤ b } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ im z ≤ b } := by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using
    frontier_re_prod_im (Ici a) (Iic b)
#align complex.frontier_set_of_le_re_and_im_le Complex.frontier_setOf_le_re_and_im_le

end Complex

open Complex Metric

variable {s t : Set ℝ}

/- warning: is_open.re_prod_im -> IsOpen.reProdIm is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (IsOpen.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) -> (IsOpen.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t) -> (IsOpen.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.Set.reProdIm s t))
but is expected to have type
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (IsOpen.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) -> (IsOpen.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t) -> (IsOpen.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.Set.reProdIm s t))
Case conversion may be inaccurate. Consider using '#align is_open.re_prod_im IsOpen.reProdImₓ'. -/
theorem IsOpen.reProdIm (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)
#align is_open.re_prod_im IsOpen.reProdIm

/- warning: is_closed.re_prod_im -> IsClosed.reProdIm is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (IsClosed.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) -> (IsClosed.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t) -> (IsClosed.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))))) (Complex.Set.reProdIm s t))
but is expected to have type
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (IsClosed.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) s) -> (IsClosed.{0} Real (UniformSpace.toTopologicalSpace.{0} Real (PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace)) t) -> (IsClosed.{0} Complex (UniformSpace.toTopologicalSpace.{0} Complex (PseudoMetricSpace.toUniformSpace.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))))) (Complex.Set.reProdIm s t))
Case conversion may be inaccurate. Consider using '#align is_closed.re_prod_im IsClosed.reProdImₓ'. -/
theorem IsClosed.reProdIm (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)
#align is_closed.re_prod_im IsClosed.reProdIm

/- warning: metric.bounded.re_prod_im -> Metric.Bounded.reProdIm is a dubious translation:
lean 3 declaration is
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Metric.Bounded.{0} Real Real.pseudoMetricSpace t) -> (Metric.Bounded.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSemiNormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.normedField)))) (Complex.Set.reProdIm s t))
but is expected to have type
  forall {s : Set.{0} Real} {t : Set.{0} Real}, (Metric.Bounded.{0} Real Real.pseudoMetricSpace s) -> (Metric.Bounded.{0} Real Real.pseudoMetricSpace t) -> (Metric.Bounded.{0} Complex (SeminormedRing.toPseudoMetricSpace.{0} Complex (SeminormedCommRing.toSeminormedRing.{0} Complex (NormedCommRing.toSeminormedCommRing.{0} Complex (NormedField.toNormedCommRing.{0} Complex Complex.instNormedFieldComplex)))) (Complex.Set.reProdIm s t))
Case conversion may be inaccurate. Consider using '#align metric.bounded.re_prod_im Metric.Bounded.reProdImₓ'. -/
theorem Metric.Bounded.reProdIm (hs : Bounded s) (ht : Bounded t) : Bounded (s ×ℂ t) :=
  antilipschitz_equivRealProd.bounded_preimage (hs.Prod ht)
#align metric.bounded.re_prod_im Metric.Bounded.reProdIm

