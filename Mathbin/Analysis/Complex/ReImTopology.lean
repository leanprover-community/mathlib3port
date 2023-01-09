/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module analysis.complex.re_im_topology
! leanprover-community/mathlib commit 247a102b14f3cebfee126293341af5f6bed00237
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Complex.Basic
import Mathbin.Topology.FiberBundle.IsHomeomorphicTrivialBundle

/-!
# Closure, interior, and frontier of preimages under `re` and `im`

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

/-- `complex.re` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem is_homeomorphic_trivial_fiber_bundle_re : IsHomeomorphicTrivialFiberBundle ℝ re :=
  ⟨equivRealProdₗ.toHomeomorph, fun z => rfl⟩
#align
  complex.is_homeomorphic_trivial_fiber_bundle_re Complex.is_homeomorphic_trivial_fiber_bundle_re

/-- `complex.im` turns `ℂ` into a trivial topological fiber bundle over `ℝ`. -/
theorem is_homeomorphic_trivial_fiber_bundle_im : IsHomeomorphicTrivialFiberBundle ℝ im :=
  ⟨equivRealProdₗ.toHomeomorph.trans (Homeomorph.prodComm ℝ ℝ), fun z => rfl⟩
#align
  complex.is_homeomorphic_trivial_fiber_bundle_im Complex.is_homeomorphic_trivial_fiber_bundle_im

theorem is_open_map_re : IsOpenMap re :=
  is_homeomorphic_trivial_fiber_bundle_re.is_open_map_proj
#align complex.is_open_map_re Complex.is_open_map_re

theorem is_open_map_im : IsOpenMap im :=
  is_homeomorphic_trivial_fiber_bundle_im.is_open_map_proj
#align complex.is_open_map_im Complex.is_open_map_im

theorem quotient_map_re : QuotientMap re :=
  is_homeomorphic_trivial_fiber_bundle_re.quotient_map_proj
#align complex.quotient_map_re Complex.quotient_map_re

theorem quotient_map_im : QuotientMap im :=
  is_homeomorphic_trivial_fiber_bundle_im.quotient_map_proj
#align complex.quotient_map_im Complex.quotient_map_im

theorem interior_preimage_re (s : Set ℝ) : interior (re ⁻¹' s) = re ⁻¹' interior s :=
  (is_open_map_re.preimage_interior_eq_interior_preimage continuous_re _).symm
#align complex.interior_preimage_re Complex.interior_preimage_re

theorem interior_preimage_im (s : Set ℝ) : interior (im ⁻¹' s) = im ⁻¹' interior s :=
  (is_open_map_im.preimage_interior_eq_interior_preimage continuous_im _).symm
#align complex.interior_preimage_im Complex.interior_preimage_im

theorem closure_preimage_re (s : Set ℝ) : closure (re ⁻¹' s) = re ⁻¹' closure s :=
  (is_open_map_re.preimage_closure_eq_closure_preimage continuous_re _).symm
#align complex.closure_preimage_re Complex.closure_preimage_re

theorem closure_preimage_im (s : Set ℝ) : closure (im ⁻¹' s) = im ⁻¹' closure s :=
  (is_open_map_im.preimage_closure_eq_closure_preimage continuous_im _).symm
#align complex.closure_preimage_im Complex.closure_preimage_im

theorem frontier_preimage_re (s : Set ℝ) : frontier (re ⁻¹' s) = re ⁻¹' frontier s :=
  (is_open_map_re.preimage_frontier_eq_frontier_preimage continuous_re _).symm
#align complex.frontier_preimage_re Complex.frontier_preimage_re

theorem frontier_preimage_im (s : Set ℝ) : frontier (im ⁻¹' s) = im ⁻¹' frontier s :=
  (is_open_map_im.preimage_frontier_eq_frontier_preimage continuous_im _).symm
#align complex.frontier_preimage_im Complex.frontier_preimage_im

@[simp]
theorem interior_set_of_re_le (a : ℝ) : interior { z : ℂ | z.re ≤ a } = { z | z.re < a } := by
  simpa only [interior_Iic] using interior_preimage_re (Iic a)
#align complex.interior_set_of_re_le Complex.interior_set_of_re_le

@[simp]
theorem interior_set_of_im_le (a : ℝ) : interior { z : ℂ | z.im ≤ a } = { z | z.im < a } := by
  simpa only [interior_Iic] using interior_preimage_im (Iic a)
#align complex.interior_set_of_im_le Complex.interior_set_of_im_le

@[simp]
theorem interior_set_of_le_re (a : ℝ) : interior { z : ℂ | a ≤ z.re } = { z | a < z.re } := by
  simpa only [interior_Ici] using interior_preimage_re (Ici a)
#align complex.interior_set_of_le_re Complex.interior_set_of_le_re

@[simp]
theorem interior_set_of_le_im (a : ℝ) : interior { z : ℂ | a ≤ z.im } = { z | a < z.im } := by
  simpa only [interior_Ici] using interior_preimage_im (Ici a)
#align complex.interior_set_of_le_im Complex.interior_set_of_le_im

@[simp]
theorem closure_set_of_re_lt (a : ℝ) : closure { z : ℂ | z.re < a } = { z | z.re ≤ a } := by
  simpa only [closure_Iio] using closure_preimage_re (Iio a)
#align complex.closure_set_of_re_lt Complex.closure_set_of_re_lt

@[simp]
theorem closure_set_of_im_lt (a : ℝ) : closure { z : ℂ | z.im < a } = { z | z.im ≤ a } := by
  simpa only [closure_Iio] using closure_preimage_im (Iio a)
#align complex.closure_set_of_im_lt Complex.closure_set_of_im_lt

@[simp]
theorem closure_set_of_lt_re (a : ℝ) : closure { z : ℂ | a < z.re } = { z | a ≤ z.re } := by
  simpa only [closure_Ioi] using closure_preimage_re (Ioi a)
#align complex.closure_set_of_lt_re Complex.closure_set_of_lt_re

@[simp]
theorem closure_set_of_lt_im (a : ℝ) : closure { z : ℂ | a < z.im } = { z | a ≤ z.im } := by
  simpa only [closure_Ioi] using closure_preimage_im (Ioi a)
#align complex.closure_set_of_lt_im Complex.closure_set_of_lt_im

@[simp]
theorem frontier_set_of_re_le (a : ℝ) : frontier { z : ℂ | z.re ≤ a } = { z | z.re = a } := by
  simpa only [frontier_Iic] using frontier_preimage_re (Iic a)
#align complex.frontier_set_of_re_le Complex.frontier_set_of_re_le

@[simp]
theorem frontier_set_of_im_le (a : ℝ) : frontier { z : ℂ | z.im ≤ a } = { z | z.im = a } := by
  simpa only [frontier_Iic] using frontier_preimage_im (Iic a)
#align complex.frontier_set_of_im_le Complex.frontier_set_of_im_le

@[simp]
theorem frontier_set_of_le_re (a : ℝ) : frontier { z : ℂ | a ≤ z.re } = { z | z.re = a } := by
  simpa only [frontier_Ici] using frontier_preimage_re (Ici a)
#align complex.frontier_set_of_le_re Complex.frontier_set_of_le_re

@[simp]
theorem frontier_set_of_le_im (a : ℝ) : frontier { z : ℂ | a ≤ z.im } = { z | z.im = a } := by
  simpa only [frontier_Ici] using frontier_preimage_im (Ici a)
#align complex.frontier_set_of_le_im Complex.frontier_set_of_le_im

@[simp]
theorem frontier_set_of_re_lt (a : ℝ) : frontier { z : ℂ | z.re < a } = { z | z.re = a } := by
  simpa only [frontier_Iio] using frontier_preimage_re (Iio a)
#align complex.frontier_set_of_re_lt Complex.frontier_set_of_re_lt

@[simp]
theorem frontier_set_of_im_lt (a : ℝ) : frontier { z : ℂ | z.im < a } = { z | z.im = a } := by
  simpa only [frontier_Iio] using frontier_preimage_im (Iio a)
#align complex.frontier_set_of_im_lt Complex.frontier_set_of_im_lt

@[simp]
theorem frontier_set_of_lt_re (a : ℝ) : frontier { z : ℂ | a < z.re } = { z | z.re = a } := by
  simpa only [frontier_Ioi] using frontier_preimage_re (Ioi a)
#align complex.frontier_set_of_lt_re Complex.frontier_set_of_lt_re

@[simp]
theorem frontier_set_of_lt_im (a : ℝ) : frontier { z : ℂ | a < z.im } = { z | z.im = a } := by
  simpa only [frontier_Ioi] using frontier_preimage_im (Ioi a)
#align complex.frontier_set_of_lt_im Complex.frontier_set_of_lt_im

theorem closure_re_prod_im (s t : Set ℝ) : closure (s ×ℂ t) = closure s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equiv_real_prodₗ.symm.to_homeomorph.surjective,
    equiv_real_prodₗ.symm.to_homeomorph.preimage_closure] using @closure_prod_eq _ _ _ _ s t
#align complex.closure_re_prod_im Complex.closure_re_prod_im

theorem interior_re_prod_im (s t : Set ℝ) : interior (s ×ℂ t) = interior s ×ℂ interior t := by
  rw [re_prod_im, re_prod_im, interior_inter, interior_preimage_re, interior_preimage_im]
#align complex.interior_re_prod_im Complex.interior_re_prod_im

theorem frontier_re_prod_im (s t : Set ℝ) :
    frontier (s ×ℂ t) = closure s ×ℂ frontier t ∪ frontier s ×ℂ closure t := by
  simpa only [← preimage_eq_preimage equiv_real_prodₗ.symm.to_homeomorph.surjective,
    equiv_real_prodₗ.symm.to_homeomorph.preimage_frontier] using frontier_prod_eq s t
#align complex.frontier_re_prod_im Complex.frontier_re_prod_im

theorem frontier_set_of_le_re_and_le_im (a b : ℝ) :
    frontier { z | a ≤ re z ∧ b ≤ im z } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ b ≤ im z } := by
  simpa only [closure_Ici, frontier_Ici] using frontier_re_prod_im (Ici a) (Ici b)
#align complex.frontier_set_of_le_re_and_le_im Complex.frontier_set_of_le_re_and_le_im

theorem frontier_set_of_le_re_and_im_le (a b : ℝ) :
    frontier { z | a ≤ re z ∧ im z ≤ b } = { z | a ≤ re z ∧ im z = b ∨ re z = a ∧ im z ≤ b } := by
  simpa only [closure_Ici, closure_Iic, frontier_Ici, frontier_Iic] using
    frontier_re_prod_im (Ici a) (Iic b)
#align complex.frontier_set_of_le_re_and_im_le Complex.frontier_set_of_le_re_and_im_le

end Complex

open Complex Metric

variable {s t : Set ℝ}

theorem IsOpen.re_prod_im (hs : IsOpen s) (ht : IsOpen t) : IsOpen (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)
#align is_open.re_prod_im IsOpen.re_prod_im

theorem IsClosed.re_prod_im (hs : IsClosed s) (ht : IsClosed t) : IsClosed (s ×ℂ t) :=
  (hs.Preimage continuous_re).inter (ht.Preimage continuous_im)
#align is_closed.re_prod_im IsClosed.re_prod_im

theorem Metric.Bounded.re_prod_im (hs : Bounded s) (ht : Bounded t) : Bounded (s ×ℂ t) :=
  equivRealProdₗ.antilipschitz.bounded_preimage (hs.Prod ht)
#align metric.bounded.re_prod_im Metric.Bounded.re_prod_im

