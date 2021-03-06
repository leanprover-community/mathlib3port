/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudriashov
-/
import Mathbin.Analysis.Convex.Combination
import Mathbin.Analysis.Convex.Function

/-!
# Jensen's inequality and maximum principle for convex functions

In this file, we prove the finite Jensen inequality and the finite maximum principle for convex
functions. The integral versions are to be found in `analysis.convex.integral`.

## Main declarations

Jensen's inequalities:
* `convex_on.map_center_mass_le`, `convex_on.map_sum_le`: Convex Jensen's inequality. The image of a
  convex combination of points under a convex function is less than the convex combination of the
  images.
* `concave_on.le_map_center_mass`, `concave_on.le_map_sum`: Concave Jensen's inequality.

As corollaries, we get:
* `convex_on.exists_ge_of_mem_convex_hull `: Maximum principle for convex functions.
* `concave_on.exists_le_of_mem_convex_hull`: Minimum principle for concave functions.
-/


open Finset LinearMap Set

open BigOperators Classical Convex Pointwise

variable {π E F Ξ² ΞΉ : Type _}

/-! ### Jensen's inequality -/


section Jensen

variable [LinearOrderedField π] [AddCommGroupβ E] [OrderedAddCommGroup Ξ²] [Module π E] [Module π Ξ²] [OrderedSmul π Ξ²]
  {s : Set E} {f : E β Ξ²} {t : Finset ΞΉ} {w : ΞΉ β π} {p : ΞΉ β E}

/-- Convex **Jensen's inequality**, `finset.center_mass` version. -/
theorem ConvexOn.map_center_mass_le (hf : ConvexOn π s f) (hβ : β, β i β t, β, 0 β€ w i) (hβ : 0 < β i in t, w i)
    (hmem : β, β i β t, β, p i β s) : f (t.centerMass w p) β€ t.centerMass w (f β p) := by
  have hmem' : β, β i β t, β, (p i, (f β p) i) β { p : E Γ Ξ² | p.1 β s β§ f p.1 β€ p.2 } := fun i hi =>
    β¨hmem i hi, le_rflβ©
  convert (hf.convex_epigraph.center_mass_mem hβ hβ hmem').2 <;>
    simp only [β center_mass, β Function.comp, β Prod.smul_fst, β Prod.fst_sum, β Prod.smul_snd, β Prod.snd_sum]

/-- Concave **Jensen's inequality**, `finset.center_mass` version. -/
theorem ConcaveOn.le_map_center_mass (hf : ConcaveOn π s f) (hβ : β, β i β t, β, 0 β€ w i) (hβ : 0 < β i in t, w i)
    (hmem : β, β i β t, β, p i β s) : t.centerMass w (f β p) β€ f (t.centerMass w p) :=
  @ConvexOn.map_center_mass_le π E Ξ²α΅α΅ _ _ _ _ _ _ _ _ _ _ _ _ hf hβ hβ hmem

/-- Convex **Jensen's inequality**, `finset.sum` version. -/
theorem ConvexOn.map_sum_le (hf : ConvexOn π s f) (hβ : β, β i β t, β, 0 β€ w i) (hβ : (β i in t, w i) = 1)
    (hmem : β, β i β t, β, p i β s) : f (β i in t, w i β’ p i) β€ β i in t, w i β’ f (p i) := by
  simpa only [β center_mass, β hβ, β inv_one, β one_smul] using hf.map_center_mass_le hβ (hβ.symm βΈ zero_lt_one) hmem

/-- Concave **Jensen's inequality**, `finset.sum` version. -/
theorem ConcaveOn.le_map_sum (hf : ConcaveOn π s f) (hβ : β, β i β t, β, 0 β€ w i) (hβ : (β i in t, w i) = 1)
    (hmem : β, β i β t, β, p i β s) : (β i in t, w i β’ f (p i)) β€ f (β i in t, w i β’ p i) :=
  @ConvexOn.map_sum_le π E Ξ²α΅α΅ _ _ _ _ _ _ _ _ _ _ _ _ hf hβ hβ hmem

end Jensen

/-! ### Maximum principle -/


section MaximumPrinciple

variable [LinearOrderedField π] [AddCommGroupβ E] [LinearOrderedAddCommGroup Ξ²] [Module π E] [Module π Ξ²]
  [OrderedSmul π Ξ²] {s : Set E} {f : E β Ξ²} {t : Finset ΞΉ} {w : ΞΉ β π} {p : ΞΉ β E}

/-- If a function `f` is convex on `s`, then the value it takes at some center of mass of points of
`s` is less than the value it takes on one of those points. -/
theorem ConvexOn.exists_ge_of_center_mass (h : ConvexOn π s f) (hwβ : β, β i β t, β, 0 β€ w i) (hwβ : 0 < β i in t, w i)
    (hp : β, β i β t, β, p i β s) : β i β t, f (t.centerMass w p) β€ f (p i) := by
  set y := t.center_mass w p
  suffices h : β i β t.filter fun i => w i β  0, w i β’ f y β€ w i β’ (f β p) i
  Β· obtain β¨i, hi, hfiβ© := h
    rw [mem_filter] at hi
    exact β¨i, hi.1, (smul_le_smul_iff_of_pos <| (hwβ i hi.1).lt_of_ne hi.2.symm).1 hfiβ©
    
  have hw' : (0 : π) < β i in filter (fun i => w i β  0) t, w i := by
    rwa [sum_filter_ne_zero]
  refine' exists_le_of_sum_le (nonempty_of_sum_ne_zero hw'.ne') _
  rw [β sum_smul, β smul_le_smul_iff_of_pos (inv_pos.2 hw'), inv_smul_smulβ hw'.ne', β Finset.centerMass,
    Finset.center_mass_filter_ne_zero]
  exact h.map_center_mass_le hwβ hwβ hp
  infer_instance

/-- If a function `f` is concave on `s`, then the value it takes at some center of mass of points of
`s` is greater than the value it takes on one of those points. -/
theorem ConcaveOn.exists_le_of_center_mass (h : ConcaveOn π s f) (hwβ : β, β i β t, β, 0 β€ w i)
    (hwβ : 0 < β i in t, w i) (hp : β, β i β t, β, p i β s) : β i β t, f (p i) β€ f (t.centerMass w p) :=
  @ConvexOn.exists_ge_of_center_mass π E Ξ²α΅α΅ _ _ _ _ _ _ _ _ _ _ _ _ h hwβ hwβ hp

/-- Maximum principle for convex functions. If a function `f` is convex on the convex hull of `s`,
then the eventual maximum of `f` on `convex_hull π s` lies in `s`. -/
theorem ConvexOn.exists_ge_of_mem_convex_hull (hf : ConvexOn π (convexHull π s) f) {x} (hx : x β convexHull π s) :
    β y β s, f x β€ f y := by
  rw [_root_.convex_hull_eq] at hx
  obtain β¨Ξ±, t, w, p, hwβ, hwβ, hp, rflβ© := hx
  rcases hf.exists_ge_of_center_mass hwβ (hwβ.symm βΈ zero_lt_one) fun i hi => subset_convex_hull π s (hp i hi) with
    β¨i, hit, Hiβ©
  exact β¨p i, hp i hit, Hiβ©

/-- Minimum principle for concave functions. If a function `f` is concave on the convex hull of `s`,
then the eventual minimum of `f` on `convex_hull π s` lies in `s`. -/
theorem ConcaveOn.exists_le_of_mem_convex_hull (hf : ConcaveOn π (convexHull π s) f) {x} (hx : x β convexHull π s) :
    β y β s, f y β€ f x :=
  @ConvexOn.exists_ge_of_mem_convex_hull π E Ξ²α΅α΅ _ _ _ _ _ _ _ _ hf _ hx

end MaximumPrinciple

