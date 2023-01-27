/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov

! This file was ported from Lean 3 source module analysis.calculus.fderiv
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Asymptotics.AsymptoticEquivalent
import Mathbin.Analysis.Calculus.TangentCone
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.Analysis.NormedSpace.Units

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

Finally,

  `has_strict_fderiv_at f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`is_bounded_bilinear_map.has_fderiv_at` twice: first for `has_fderiv_at`, then for
`has_strict_fderiv_at`.

## Main results

In addition to the definition and basic properties of the derivative, this file contains the
usual formulas (and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps
* bounded bilinear maps
* sum of two functions
* sum of finitely many functions
* multiplication of a function by a scalar constant
* negative of a function
* subtraction of two functions
* multiplication of a function by a scalar function
* multiplication of two scalar functions
* composition of functions (the chain rule)
* inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `analysis.special_functions.trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `deriv.lean`.

## Implementation details

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`tests/differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

-/


open Filter Asymptotics ContinuousLinearMap Set Metric

open TopologicalSpace Classical Nnreal Filter Asymptotics Ennreal

noncomputable section

section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type _} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `has_fderiv_at`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `has_fderiv_within_at`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
def HasFderivAtFilter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : Filter E) :=
  (fun x' => f x' - f x - f' (x' - x)) =o[L] fun x' => x' - x
#align has_fderiv_at_filter HasFderivAtFilter

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
def HasFderivWithinAt (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (x : E) :=
  HasFderivAtFilter f f' x (𝓝[s] x)
#align has_fderiv_within_at HasFderivWithinAt

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
def HasFderivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  HasFderivAtFilter f f' x (𝓝 x)
#align has_fderiv_at HasFderivAt

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def HasStrictFderivAt (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
  (fun p : E × E => f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] fun p : E × E => p.1 - p.2
#align has_strict_fderiv_at HasStrictFderivAt

variable (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
def DifferentiableWithinAt (f : E → F) (s : Set E) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFderivWithinAt f f' s x
#align differentiable_within_at DifferentiableWithinAt

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
def DifferentiableAt (f : E → F) (x : E) :=
  ∃ f' : E →L[𝕜] F, HasFderivAt f f' x
#align differentiable_at DifferentiableAt

/-- If `f` has a derivative at `x` within `s`, then `fderiv_within 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. -/
def fderivWithin (f : E → F) (s : Set E) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFderivWithinAt f f' s x then Classical.choose h else 0
#align fderiv_within fderivWithin

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
  if h : ∃ f', HasFderivAt f f' x then Classical.choose h else 0
#align fderiv fderiv

/-- `differentiable_on 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
def DifferentiableOn (f : E → F) (s : Set E) :=
  ∀ x ∈ s, DifferentiableWithinAt 𝕜 f s x
#align differentiable_on DifferentiableOn

/-- `differentiable 𝕜 f` means that `f` is differentiable at any point. -/
def Differentiable (f : E → F) :=
  ∀ x, DifferentiableAt 𝕜 f x
#align differentiable Differentiable

variable {𝕜}

variable {f f₀ f₁ g : E → F}

variable {f' f₀' f₁' g' : E →L[𝕜] F}

variable (e : E →L[𝕜] F)

variable {x : E}

variable {s t : Set E}

variable {L L₁ L₂ : Filter E}

theorem fderivWithin_zero_of_not_differentiableWithinAt (h : ¬DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 f s x = 0 :=
  by
  have : ¬∃ f', HasFderivWithinAt f f' s x := h
  simp [fderivWithin, this]
#align fderiv_within_zero_of_not_differentiable_within_at fderivWithin_zero_of_not_differentiableWithinAt

theorem fderiv_zero_of_not_differentiableAt (h : ¬DifferentiableAt 𝕜 f x) : fderiv 𝕜 f x = 0 :=
  by
  have : ¬∃ f', HasFderivAt f f' x := h
  simp [fderiv, this]
#align fderiv_zero_of_not_differentiable_at fderiv_zero_of_not_differentiableAt

section DerivativeUniqueness

/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/
/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem HasFderivWithinAt.lim (h : HasFderivWithinAt f f' s x) {α : Type _} (l : Filter α)
    {c : α → 𝕜} {d : α → E} {v : E} (dtop : ∀ᶠ n in l, x + d n ∈ s)
    (clim : Tendsto (fun n => ‖c n‖) l atTop) (cdlim : Tendsto (fun n => c n • d n) l (𝓝 v)) :
    Tendsto (fun n => c n • (f (x + d n) - f x)) l (𝓝 (f' v)) :=
  by
  have tendsto_arg : tendsto (fun n => x + d n) l (𝓝[s] x) :=
    by
    conv in 𝓝[s] x => rw [← add_zero x]
    rw [nhdsWithin, tendsto_inf]
    constructor
    · apply tendsto_const_nhds.add (tangentConeAt.lim_zero l clim cdlim)
    · rwa [tendsto_principal]
  have : (fun y => f y - f x - f' (y - x)) =o[𝓝[s] x] fun y => y - x := h
  have : (fun n => f (x + d n) - f x - f' (x + d n - x)) =o[l] fun n => x + d n - x :=
    this.comp_tendsto tendsto_arg
  have : (fun n => f (x + d n) - f x - f' (d n)) =o[l] d := by simpa only [add_sub_cancel']
  have : (fun n => c n • (f (x + d n) - f x - f' (d n))) =o[l] fun n => c n • d n :=
    (is_O_refl c l).smul_is_o this
  have : (fun n => c n • (f (x + d n) - f x - f' (d n))) =o[l] fun n => (1 : ℝ) :=
    this.trans_is_O (cdlim.is_O_one ℝ)
  have L1 : tendsto (fun n => c n • (f (x + d n) - f x - f' (d n))) l (𝓝 0) :=
    (is_o_one_iff ℝ).1 this
  have L2 : tendsto (fun n => f' (c n • d n)) l (𝓝 (f' v)) :=
    tendsto.comp f'.cont.continuous_at cdlim
  have L3 :
    tendsto (fun n => c n • (f (x + d n) - f x - f' (d n)) + f' (c n • d n)) l (𝓝 (0 + f' v)) :=
    L1.add L2
  have :
    (fun n => c n • (f (x + d n) - f x - f' (d n)) + f' (c n • d n)) = fun n =>
      c n • (f (x + d n) - f x) :=
    by
    ext n
    simp [smul_add, smul_sub]
  rwa [this, zero_add] at L3
#align has_fderiv_within_at.lim HasFderivWithinAt.lim

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem HasFderivWithinAt.unique_on (hf : HasFderivWithinAt f f' s x)
    (hg : HasFderivWithinAt f f₁' s x) : EqOn f' f₁' (tangentConeAt 𝕜 s x) :=
  fun y ⟨c, d, dtop, clim, cdlim⟩ =>
  tendsto_nhds_unique (hf.lim atTop dtop clim cdlim) (hg.lim atTop dtop clim cdlim)
#align has_fderiv_within_at.unique_on HasFderivWithinAt.unique_on

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem UniqueDiffWithinAt.eq (H : UniqueDiffWithinAt 𝕜 s x) (hf : HasFderivWithinAt f f' s x)
    (hg : HasFderivWithinAt f f₁' s x) : f' = f₁' :=
  ContinuousLinearMap.ext_on H.1 (hf.unique_on hg)
#align unique_diff_within_at.eq UniqueDiffWithinAt.eq

theorem UniqueDiffOn.eq (H : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (h : HasFderivWithinAt f f' s x)
    (h₁ : HasFderivWithinAt f f₁' s x) : f' = f₁' :=
  (H x hx).Eq h h₁
#align unique_diff_on.eq UniqueDiffOn.eq

end DerivativeUniqueness

section FderivProperties

/-! ### Basic properties of the derivative -/


theorem hasFderivAtFilter_iff_tendsto :
    HasFderivAtFilter f f' x L ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) :=
  by
  have h : ∀ x', ‖x' - x‖ = 0 → ‖f x' - f x - f' (x' - x)‖ = 0 := fun x' hx' =>
    by
    rw [sub_eq_zero.1 (norm_eq_zero.1 hx')]
    simp
  unfold HasFderivAtFilter
  rw [← is_o_norm_left, ← is_o_norm_right, is_o_iff_tendsto h]
  exact tendsto_congr fun _ => div_eq_inv_mul _ _
#align has_fderiv_at_filter_iff_tendsto hasFderivAtFilter_iff_tendsto

theorem hasFderivWithinAt_iff_tendsto :
    HasFderivWithinAt f f' s x ↔
      Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) :=
  hasFderivAtFilter_iff_tendsto
#align has_fderiv_within_at_iff_tendsto hasFderivWithinAt_iff_tendsto

theorem hasFderivAt_iff_tendsto :
    HasFderivAt f f' x ↔ Tendsto (fun x' => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) :=
  hasFderivAtFilter_iff_tendsto
#align has_fderiv_at_iff_tendsto hasFderivAt_iff_tendsto

theorem hasFderivAt_iff_isO_nhds_zero :
    HasFderivAt f f' x ↔ (fun h : E => f (x + h) - f x - f' h) =o[𝓝 0] fun h => h :=
  by
  rw [HasFderivAt, HasFderivAtFilter, ← map_add_left_nhds_zero x, is_o_map]
  simp [(· ∘ ·)]
#align has_fderiv_at_iff_is_o_nhds_zero hasFderivAt_iff_isO_nhds_zero

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
theorem HasFderivAt.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFderivAt f f' x₀)
    {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C :=
  by
  refine' le_of_forall_pos_le_add fun ε ε0 => op_norm_le_of_nhds_zero _ _
  exact add_nonneg hC₀ ε0.le
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip
  filter_upwards [is_o_iff.1 (hasFderivAt_iff_isO_nhds_zero.1 hf) ε0, hlip]with y hy hyC
  rw [add_sub_cancel'] at hyC
  calc
    ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ := norm_le_insert _ _
    _ ≤ C * ‖y‖ + ε * ‖y‖ := add_le_add hyC hy
    _ = (C + ε) * ‖y‖ := (add_mul _ _ _).symm
    
#align has_fderiv_at.le_of_lip' HasFderivAt.le_of_lip'

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. -/
theorem HasFderivAt.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : HasFderivAt f f' x₀)
    {s : Set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖f'‖ ≤ C :=
  by
  refine' hf.le_of_lip' C.coe_nonneg _
  filter_upwards [hs]with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs)
#align has_fderiv_at.le_of_lip HasFderivAt.le_of_lip

theorem HasFderivAtFilter.mono (h : HasFderivAtFilter f f' x L₂) (hst : L₁ ≤ L₂) :
    HasFderivAtFilter f f' x L₁ :=
  h.mono hst
#align has_fderiv_at_filter.mono HasFderivAtFilter.mono

theorem HasFderivWithinAt.mono_of_mem (h : HasFderivWithinAt f f' t x) (hst : t ∈ 𝓝[s] x) :
    HasFderivWithinAt f f' s x :=
  h.mono <| nhdsWithin_le_iff.mpr hst
#align has_fderiv_within_at.mono_of_mem HasFderivWithinAt.mono_of_mem

theorem HasFderivWithinAt.mono (h : HasFderivWithinAt f f' t x) (hst : s ⊆ t) :
    HasFderivWithinAt f f' s x :=
  h.mono <| nhdsWithin_mono _ hst
#align has_fderiv_within_at.mono HasFderivWithinAt.mono

theorem HasFderivAt.hasFderivAtFilter (h : HasFderivAt f f' x) (hL : L ≤ 𝓝 x) :
    HasFderivAtFilter f f' x L :=
  h.mono hL
#align has_fderiv_at.has_fderiv_at_filter HasFderivAt.hasFderivAtFilter

theorem HasFderivAt.hasFderivWithinAt (h : HasFderivAt f f' x) : HasFderivWithinAt f f' s x :=
  h.HasFderivAtFilter inf_le_left
#align has_fderiv_at.has_fderiv_within_at HasFderivAt.hasFderivWithinAt

theorem HasFderivWithinAt.differentiableWithinAt (h : HasFderivWithinAt f f' s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  ⟨f', h⟩
#align has_fderiv_within_at.differentiable_within_at HasFderivWithinAt.differentiableWithinAt

theorem HasFderivAt.differentiableAt (h : HasFderivAt f f' x) : DifferentiableAt 𝕜 f x :=
  ⟨f', h⟩
#align has_fderiv_at.differentiable_at HasFderivAt.differentiableAt

@[simp]
theorem hasFderivWithinAt_univ : HasFderivWithinAt f f' univ x ↔ HasFderivAt f f' x :=
  by
  simp only [HasFderivWithinAt, nhdsWithin_univ]
  rfl
#align has_fderiv_within_at_univ hasFderivWithinAt_univ

alias hasFderivWithinAt_univ ↔ HasFderivWithinAt.hasFderivAt_of_univ _
#align has_fderiv_within_at.has_fderiv_at_of_univ HasFderivWithinAt.hasFderivAt_of_univ

theorem hasFderivWithinAt_insert {y : E} {g' : E →L[𝕜] F} :
    HasFderivWithinAt g g' (insert y s) x ↔ HasFderivWithinAt g g' s x :=
  by
  rcases eq_or_ne x y with (rfl | h)
  · simp_rw [HasFderivWithinAt, HasFderivAtFilter]
    apply Asymptotics.isO_insert
    simp only [sub_self, g'.map_zero]
  refine' ⟨fun h => h.mono <| subset_insert y s, fun hg => hg.mono_of_mem _⟩
  simp_rw [nhdsWithin_insert_of_ne h, self_mem_nhdsWithin]
#align has_fderiv_within_at_insert hasFderivWithinAt_insert

alias hasFderivWithinAt_insert ↔ HasFderivWithinAt.of_insert HasFderivWithinAt.insert'
#align has_fderiv_within_at.of_insert HasFderivWithinAt.of_insert
#align has_fderiv_within_at.insert' HasFderivWithinAt.insert'

theorem HasFderivWithinAt.insert {g' : E →L[𝕜] F} (h : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt g g' (insert x s) x :=
  h.insert'
#align has_fderiv_within_at.insert HasFderivWithinAt.insert

theorem HasStrictFderivAt.isO_sub (hf : HasStrictFderivAt f f' x) :
    (fun p : E × E => f p.1 - f p.2) =O[𝓝 (x, x)] fun p : E × E => p.1 - p.2 :=
  hf.IsO.congr_of_sub.2 (f'.is_O_comp _ _)
#align has_strict_fderiv_at.is_O_sub HasStrictFderivAt.isO_sub

theorem HasFderivAtFilter.isO_sub (h : HasFderivAtFilter f f' x L) :
    (fun x' => f x' - f x) =O[L] fun x' => x' - x :=
  h.IsO.congr_of_sub.2 (f'.is_O_sub _ _)
#align has_fderiv_at_filter.is_O_sub HasFderivAtFilter.isO_sub

protected theorem HasStrictFderivAt.hasFderivAt (hf : HasStrictFderivAt f f' x) :
    HasFderivAt f f' x := by
  rw [HasFderivAt, HasFderivAtFilter, is_o_iff]
  exact fun c hc => tendsto_id.prod_mk_nhds tendsto_const_nhds (is_o_iff.1 hf hc)
#align has_strict_fderiv_at.has_fderiv_at HasStrictFderivAt.hasFderivAt

protected theorem HasStrictFderivAt.differentiableAt (hf : HasStrictFderivAt f f' x) :
    DifferentiableAt 𝕜 f x :=
  hf.HasFderivAt.DifferentiableAt
#align has_strict_fderiv_at.differentiable_at HasStrictFderivAt.differentiableAt

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
theorem HasStrictFderivAt.exists_lipschitzOnWith_of_nnnorm_lt (hf : HasStrictFderivAt f f' x)
    (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, LipschitzOnWith K f s :=
  by
  have := hf.add_is_O_with (f'.is_O_with_comp _ _) hK
  simp only [sub_add_cancel, is_O_with] at this
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩
  exact
    ⟨U, Uo.mem_nhds xU, lipschitzOnWith_iff_norm_sub_le.2 fun x hx y hy => hU (mk_mem_prod hx hy)⟩
#align has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt HasStrictFderivAt.exists_lipschitzOnWith_of_nnnorm_lt

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt` for a
more precise statement. -/
theorem HasStrictFderivAt.exists_lipschitzOnWith (hf : HasStrictFderivAt f f' x) :
    ∃ K, ∃ s ∈ 𝓝 x, LipschitzOnWith K f s :=
  (exists_gt _).imp hf.exists_lipschitz_on_with_of_nnnorm_lt
#align has_strict_fderiv_at.exists_lipschitz_on_with HasStrictFderivAt.exists_lipschitzOnWith

/-- Directional derivative agrees with `has_fderiv`. -/
theorem HasFderivAt.lim (hf : HasFderivAt f f' x) (v : E) {α : Type _} {c : α → 𝕜} {l : Filter α}
    (hc : Tendsto (fun n => ‖c n‖) l atTop) :
    Tendsto (fun n => c n • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) :=
  by
  refine' (hasFderivWithinAt_univ.2 hf).lim _ univ_mem hc _
  intro U hU
  refine' (eventually_ne_of_tendsto_norm_atTop hc (0 : 𝕜)).mono fun y hy => _
  convert mem_of_mem_nhds hU
  dsimp only
  rw [← mul_smul, mul_inv_cancel hy, one_smul]
#align has_fderiv_at.lim HasFderivAt.lim

theorem HasFderivAt.unique (h₀ : HasFderivAt f f₀' x) (h₁ : HasFderivAt f f₁' x) : f₀' = f₁' :=
  by
  rw [← hasFderivWithinAt_univ] at h₀ h₁
  exact unique_diff_within_at_univ.eq h₀ h₁
#align has_fderiv_at.unique HasFderivAt.unique

theorem hasFderivWithinAt_inter' (h : t ∈ 𝓝[s] x) :
    HasFderivWithinAt f f' (s ∩ t) x ↔ HasFderivWithinAt f f' s x := by
  simp [HasFderivWithinAt, nhdsWithin_restrict'' s h]
#align has_fderiv_within_at_inter' hasFderivWithinAt_inter'

theorem hasFderivWithinAt_inter (h : t ∈ 𝓝 x) :
    HasFderivWithinAt f f' (s ∩ t) x ↔ HasFderivWithinAt f f' s x := by
  simp [HasFderivWithinAt, nhdsWithin_restrict' s h]
#align has_fderiv_within_at_inter hasFderivWithinAt_inter

theorem HasFderivWithinAt.union (hs : HasFderivWithinAt f f' s x)
    (ht : HasFderivWithinAt f f' t x) : HasFderivWithinAt f f' (s ∪ t) x :=
  by
  simp only [HasFderivWithinAt, nhdsWithin_union]
  exact hs.sup ht
#align has_fderiv_within_at.union HasFderivWithinAt.union

theorem HasFderivWithinAt.nhdsWithin (h : HasFderivWithinAt f f' s x) (ht : s ∈ 𝓝[t] x) :
    HasFderivWithinAt f f' t x :=
  (hasFderivWithinAt_inter' ht).1 (h.mono (inter_subset_right _ _))
#align has_fderiv_within_at.nhds_within HasFderivWithinAt.nhdsWithin

theorem HasFderivWithinAt.hasFderivAt (h : HasFderivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasFderivAt f f' x := by
  rwa [← univ_inter s, hasFderivWithinAt_inter hs, hasFderivWithinAt_univ] at h
#align has_fderiv_within_at.has_fderiv_at HasFderivWithinAt.hasFderivAt

theorem DifferentiableWithinAt.differentiableAt (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : s ∈ 𝓝 x) : DifferentiableAt 𝕜 f x :=
  h.imp fun f' hf' => hf'.HasFderivAt hs
#align differentiable_within_at.differentiable_at DifferentiableWithinAt.differentiableAt

theorem DifferentiableWithinAt.hasFderivWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    HasFderivWithinAt f (fderivWithin 𝕜 f s x) s x :=
  by
  dsimp only [fderivWithin]
  dsimp only [DifferentiableWithinAt] at h
  rw [dif_pos h]
  exact Classical.choose_spec h
#align differentiable_within_at.has_fderiv_within_at DifferentiableWithinAt.hasFderivWithinAt

theorem DifferentiableAt.hasFderivAt (h : DifferentiableAt 𝕜 f x) :
    HasFderivAt f (fderiv 𝕜 f x) x := by
  dsimp only [fderiv]
  dsimp only [DifferentiableAt] at h
  rw [dif_pos h]
  exact Classical.choose_spec h
#align differentiable_at.has_fderiv_at DifferentiableAt.hasFderivAt

theorem DifferentiableOn.hasFderivAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    HasFderivAt f (fderiv 𝕜 f x) x :=
  ((h x (mem_of_mem_nhds hs)).DifferentiableAt hs).HasFderivAt
#align differentiable_on.has_fderiv_at DifferentiableOn.hasFderivAt

theorem DifferentiableOn.differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    DifferentiableAt 𝕜 f x :=
  (h.HasFderivAt hs).DifferentiableAt
#align differentiable_on.differentiable_at DifferentiableOn.differentiableAt

theorem DifferentiableOn.eventually_differentiableAt (h : DifferentiableOn 𝕜 f s) (hs : s ∈ 𝓝 x) :
    ∀ᶠ y in 𝓝 x, DifferentiableAt 𝕜 f y :=
  (eventually_eventually_nhds.2 hs).mono fun y => h.DifferentiableAt
#align differentiable_on.eventually_differentiable_at DifferentiableOn.eventually_differentiableAt

theorem HasFderivAt.fderiv (h : HasFderivAt f f' x) : fderiv 𝕜 f x = f' :=
  by
  ext
  rw [h.unique h.differentiable_at.has_fderiv_at]
#align has_fderiv_at.fderiv HasFderivAt.fderiv

theorem fderiv_eq {f' : E → E →L[𝕜] F} (h : ∀ x, HasFderivAt f (f' x) x) : fderiv 𝕜 f = f' :=
  funext fun x => (h x).fderiv
#align fderiv_eq fderiv_eq

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
theorem FderivAt.le_of_lip {f : E → F} {x₀ : E} (hf : DifferentiableAt 𝕜 f x₀) {s : Set E}
    (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : LipschitzOnWith C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
  hf.HasFderivAt.le_of_lip hs hlip
#align fderiv_at.le_of_lip FderivAt.le_of_lip

theorem HasFderivWithinAt.fderivWithin (h : HasFderivWithinAt f f' s x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = f' :=
  (hxs.Eq h h.DifferentiableWithinAt.HasFderivWithinAt).symm
#align has_fderiv_within_at.fderiv_within HasFderivWithinAt.fderivWithin

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
theorem hasFderivWithinAt_of_not_mem_closure (h : x ∉ closure s) : HasFderivWithinAt f f' s x :=
  by
  simp only [mem_closure_iff_nhdsWithin_neBot, ne_bot_iff, Ne.def, not_not] at h
  simp [HasFderivWithinAt, HasFderivAtFilter, h, is_o, is_O_with]
#align has_fderiv_within_at_of_not_mem_closure hasFderivWithinAt_of_not_mem_closure

theorem DifferentiableWithinAt.mono (h : DifferentiableWithinAt 𝕜 f t x) (st : s ⊆ t) :
    DifferentiableWithinAt 𝕜 f s x := by
  rcases h with ⟨f', hf'⟩
  exact ⟨f', hf'.mono st⟩
#align differentiable_within_at.mono DifferentiableWithinAt.mono

theorem DifferentiableWithinAt.mono_of_mem (h : DifferentiableWithinAt 𝕜 f s x) {t : Set E}
    (hst : s ∈ nhdsWithin x t) : DifferentiableWithinAt 𝕜 f t x :=
  (h.HasFderivWithinAt.mono_of_mem hst).DifferentiableWithinAt
#align differentiable_within_at.mono_of_mem DifferentiableWithinAt.mono_of_mem

theorem differentiableWithinAt_univ : DifferentiableWithinAt 𝕜 f univ x ↔ DifferentiableAt 𝕜 f x :=
  by simp only [DifferentiableWithinAt, hasFderivWithinAt_univ, DifferentiableAt]
#align differentiable_within_at_univ differentiableWithinAt_univ

theorem differentiableWithinAt_inter (ht : t ∈ 𝓝 x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, HasFderivWithinAt, HasFderivAtFilter,
    nhdsWithin_restrict' s ht]
#align differentiable_within_at_inter differentiableWithinAt_inter

theorem differentiableWithinAt_inter' (ht : t ∈ 𝓝[s] x) :
    DifferentiableWithinAt 𝕜 f (s ∩ t) x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [DifferentiableWithinAt, HasFderivWithinAt, HasFderivAtFilter,
    nhdsWithin_restrict'' s ht]
#align differentiable_within_at_inter' differentiableWithinAt_inter'

theorem DifferentiableWithinAt.antimono (h : DifferentiableWithinAt 𝕜 f s x) (hst : s ⊆ t)
    (hx : s ∈ 𝓝[t] x) : DifferentiableWithinAt 𝕜 f t x := by
  rwa [← differentiableWithinAt_inter' hx, inter_eq_self_of_subset_right hst]
#align differentiable_within_at.antimono DifferentiableWithinAt.antimono

theorem HasFderivWithinAt.antimono (h : HasFderivWithinAt f f' s x) (hst : s ⊆ t)
    (hs : UniqueDiffWithinAt 𝕜 s x) (hx : s ∈ 𝓝[t] x) : HasFderivWithinAt f f' t x :=
  by
  have h' : HasFderivWithinAt f _ t x :=
    (h.differentiable_within_at.antimono hst hx).HasFderivWithinAt
  rwa [hs.eq h (h'.mono hst)]
#align has_fderiv_within_at.antimono HasFderivWithinAt.antimono

theorem DifferentiableAt.differentiableWithinAt (h : DifferentiableAt 𝕜 f x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (differentiableWithinAt_univ.2 h).mono (subset_univ _)
#align differentiable_at.differentiable_within_at DifferentiableAt.differentiableWithinAt

theorem Differentiable.differentiableAt (h : Differentiable 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h x
#align differentiable.differentiable_at Differentiable.differentiableAt

theorem DifferentiableAt.fderivWithin (h : DifferentiableAt 𝕜 f x)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  h.HasFderivAt.HasFderivWithinAt.fderivWithin hxs
#align differentiable_at.fderiv_within DifferentiableAt.fderivWithin

theorem DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t) (st : s ⊆ t) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x (st hx)).mono st
#align differentiable_on.mono DifferentiableOn.mono

theorem differentiableOn_univ : DifferentiableOn 𝕜 f univ ↔ Differentiable 𝕜 f := by
  simp only [DifferentiableOn, Differentiable, differentiableWithinAt_univ, mem_univ,
    forall_true_left]
#align differentiable_on_univ differentiableOn_univ

theorem Differentiable.differentiableOn (h : Differentiable 𝕜 f) : DifferentiableOn 𝕜 f s :=
  (differentiableOn_univ.2 h).mono (subset_univ _)
#align differentiable.differentiable_on Differentiable.differentiableOn

theorem differentiableOn_of_locally_differentiableOn
    (h : ∀ x ∈ s, ∃ u, IsOpen u ∧ x ∈ u ∧ DifferentiableOn 𝕜 f (s ∩ u)) : DifferentiableOn 𝕜 f s :=
  by
  intro x xs
  rcases h x xs with ⟨t, t_open, xt, ht⟩
  exact (differentiableWithinAt_inter (IsOpen.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
#align differentiable_on_of_locally_differentiable_on differentiableOn_of_locally_differentiableOn

theorem fderivWithin_subset (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f t x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  ((DifferentiableWithinAt.hasFderivWithinAt h).mono st).fderivWithin ht
#align fderiv_within_subset fderivWithin_subset

theorem fderivWithin_subset' (st : s ⊆ t) (ht : UniqueDiffWithinAt 𝕜 s x) (hx : s ∈ 𝓝[t] x)
    (h : DifferentiableWithinAt 𝕜 f s x) : fderivWithin 𝕜 f s x = fderivWithin 𝕜 f t x :=
  fderivWithin_subset st ht (h.antimono st hx)
#align fderiv_within_subset' fderivWithin_subset'

@[simp]
theorem fderivWithin_univ : fderivWithin 𝕜 f univ = fderiv 𝕜 f :=
  by
  ext x : 1
  by_cases h : DifferentiableAt 𝕜 f x
  · apply HasFderivWithinAt.fderivWithin _ uniqueDiffWithinAtUniv
    rw [hasFderivWithinAt_univ]
    apply h.has_fderiv_at
  · have : ¬DifferentiableWithinAt 𝕜 f univ x := by rwa [differentiableWithinAt_univ]
    rw [fderiv_zero_of_not_differentiableAt h, fderivWithin_zero_of_not_differentiableWithinAt this]
#align fderiv_within_univ fderivWithin_univ

theorem fderivWithin_inter (ht : t ∈ 𝓝 x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 f (s ∩ t) x = fderivWithin 𝕜 f s x :=
  by
  by_cases h : DifferentiableWithinAt 𝕜 f (s ∩ t) x
  · apply fderivWithin_subset (inter_subset_left _ _) _ ((differentiableWithinAt_inter ht).1 h)
    apply hs.inter ht
  · have : ¬DifferentiableWithinAt 𝕜 f s x := by rwa [← differentiableWithinAt_inter ht]
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this]
#align fderiv_within_inter fderivWithin_inter

theorem fderivWithin_of_mem_nhds (h : s ∈ 𝓝 x) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  by
  have : s = univ ∩ s := by simp only [univ_inter]
  rw [this, ← fderivWithin_univ]
  exact fderivWithin_inter h (uniqueDiffOn_univ _ (mem_univ _))
#align fderiv_within_of_mem_nhds fderivWithin_of_mem_nhds

theorem fderivWithin_of_open (hs : IsOpen s) (hx : x ∈ s) : fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  fderivWithin_of_mem_nhds (IsOpen.mem_nhds hs hx)
#align fderiv_within_of_open fderivWithin_of_open

theorem fderivWithin_eq_fderiv (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f s x = fderiv 𝕜 f x :=
  by
  rw [← fderivWithin_univ]
  exact fderivWithin_subset (subset_univ _) hs h.differentiable_within_at
#align fderiv_within_eq_fderiv fderivWithin_eq_fderiv

theorem fderiv_mem_iff {f : E → F} {s : Set (E →L[𝕜] F)} {x : E} :
    fderiv 𝕜 f x ∈ s ↔
      DifferentiableAt 𝕜 f x ∧ fderiv 𝕜 f x ∈ s ∨ ¬DifferentiableAt 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s :=
  by by_cases hx : DifferentiableAt 𝕜 f x <;> simp [fderiv_zero_of_not_differentiableAt, *]
#align fderiv_mem_iff fderiv_mem_iff

theorem fderivWithin_mem_iff {f : E → F} {t : Set E} {s : Set (E →L[𝕜] F)} {x : E} :
    fderivWithin 𝕜 f t x ∈ s ↔
      DifferentiableWithinAt 𝕜 f t x ∧ fderivWithin 𝕜 f t x ∈ s ∨
        ¬DifferentiableWithinAt 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s :=
  by
  by_cases hx : DifferentiableWithinAt 𝕜 f t x <;>
    simp [fderivWithin_zero_of_not_differentiableWithinAt, *]
#align fderiv_within_mem_iff fderivWithin_mem_iff

theorem Asymptotics.IsO.hasFderivWithinAt {s : Set E} {x₀ : E} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
    HasFderivWithinAt f (0 : E →L[𝕜] F) s x₀ := by
  simp_rw [HasFderivWithinAt, HasFderivAtFilter,
    h.eq_zero_of_norm_pow_within hx₀ <| zero_lt_one.trans hn, zero_apply, sub_zero,
    h.trans_is_o ((is_o_pow_sub_sub x₀ hn).mono nhdsWithin_le_nhds)]
#align asymptotics.is_O.has_fderiv_within_at Asymptotics.IsO.hasFderivWithinAt

theorem Asymptotics.IsO.hasFderivAt {x₀ : E} {n : ℕ} (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n)
    (hn : 1 < n) : HasFderivAt f (0 : E →L[𝕜] F) x₀ :=
  by
  rw [← nhdsWithin_univ] at h
  exact (h.has_fderiv_within_at (mem_univ _) hn).has_fderiv_at_of_univ
#align asymptotics.is_O.has_fderiv_at Asymptotics.IsO.hasFderivAt

theorem HasFderivWithinAt.isO {f : E → F} {s : Set E} {x₀ : E} {f' : E →L[𝕜] F}
    (h : HasFderivWithinAt f f' s x₀) : (fun x => f x - f x₀) =O[𝓝[s] x₀] fun x => x - x₀ := by
  simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝[s] x₀) x₀)
#align has_fderiv_within_at.is_O HasFderivWithinAt.isO

theorem HasFderivAt.isO {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : HasFderivAt f f' x₀) :
    (fun x => f x - f x₀) =O[𝓝 x₀] fun x => x - x₀ := by
  simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)
#align has_fderiv_at.is_O HasFderivAt.isO

end FderivProperties

section Continuous

/-! ### Deducing continuity from differentiability -/


theorem HasFderivAtFilter.tendsto_nhds (hL : L ≤ 𝓝 x) (h : HasFderivAtFilter f f' x L) :
    Tendsto f L (𝓝 (f x)) :=
  by
  have : tendsto (fun x' => f x' - f x) L (𝓝 0) :=
    by
    refine' h.is_O_sub.trans_tendsto (tendsto.mono_left _ hL)
    rw [← sub_self x]
    exact tendsto_id.sub tendsto_const_nhds
  have := tendsto.add this tendsto_const_nhds
  rw [zero_add (f x)] at this
  exact this.congr (by simp only [sub_add_cancel, eq_self_iff_true, forall_const])
#align has_fderiv_at_filter.tendsto_nhds HasFderivAtFilter.tendsto_nhds

theorem HasFderivWithinAt.continuousWithinAt (h : HasFderivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasFderivAtFilter.tendsto_nhds inf_le_left h
#align has_fderiv_within_at.continuous_within_at HasFderivWithinAt.continuousWithinAt

theorem HasFderivAt.continuousAt (h : HasFderivAt f f' x) : ContinuousAt f x :=
  HasFderivAtFilter.tendsto_nhds le_rfl h
#align has_fderiv_at.continuous_at HasFderivAt.continuousAt

theorem DifferentiableWithinAt.continuousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) :
    ContinuousWithinAt f s x :=
  let ⟨f', hf'⟩ := h
  hf'.ContinuousWithinAt
#align differentiable_within_at.continuous_within_at DifferentiableWithinAt.continuousWithinAt

theorem DifferentiableAt.continuousAt (h : DifferentiableAt 𝕜 f x) : ContinuousAt f x :=
  let ⟨f', hf'⟩ := h
  hf'.ContinuousAt
#align differentiable_at.continuous_at DifferentiableAt.continuousAt

theorem DifferentiableOn.continuousOn (h : DifferentiableOn 𝕜 f s) : ContinuousOn f s := fun x hx =>
  (h x hx).ContinuousWithinAt
#align differentiable_on.continuous_on DifferentiableOn.continuousOn

theorem Differentiable.continuous (h : Differentiable 𝕜 f) : Continuous f :=
  continuous_iff_continuousAt.2 fun x => (h x).ContinuousAt
#align differentiable.continuous Differentiable.continuous

protected theorem HasStrictFderivAt.continuousAt (hf : HasStrictFderivAt f f' x) :
    ContinuousAt f x :=
  hf.HasFderivAt.ContinuousAt
#align has_strict_fderiv_at.continuous_at HasStrictFderivAt.continuousAt

theorem HasStrictFderivAt.isO_sub_rev {f' : E ≃L[𝕜] F}
    (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) x) :
    (fun p : E × E => p.1 - p.2) =O[𝓝 (x, x)] fun p : E × E => f p.1 - f p.2 :=
  ((f'.is_O_comp_rev _ _).trans (hf.trans_is_O (f'.is_O_comp_rev _ _)).right_is_O_add).congr
    (fun _ => rfl) fun _ => sub_add_cancel _ _
#align has_strict_fderiv_at.is_O_sub_rev HasStrictFderivAt.isO_sub_rev

theorem HasFderivAtFilter.isO_sub_rev (hf : HasFderivAtFilter f f' x L) {C}
    (hf' : AntilipschitzWith C f') : (fun x' => x' - x) =O[L] fun x' => f x' - f x :=
  have : (fun x' => x' - x) =O[L] fun x' => f' (x' - x) :=
    isO_iff.2 ⟨C, eventually_of_forall fun x' => AddMonoidHomClass.bound_of_antilipschitz f' hf' _⟩
  (this.trans (hf.trans_is_O this).right_is_O_add).congr (fun _ => rfl) fun _ => sub_add_cancel _ _
#align has_fderiv_at_filter.is_O_sub_rev HasFderivAtFilter.isO_sub_rev

end Continuous

section congr

/-! ### congr properties of the derivative -/


theorem Filter.EventuallyEq.hasStrictFderivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
    HasStrictFderivAt f₀ f₀' x ↔ HasStrictFderivAt f₁ f₁' x :=
  by
  refine' is_o_congr ((h.prod_mk_nhds h).mono _) (eventually_of_forall fun _ => rfl)
  rintro p ⟨hp₁, hp₂⟩
  simp only [*]
#align filter.eventually_eq.has_strict_fderiv_at_iff Filter.EventuallyEq.hasStrictFderivAt_iff

theorem HasStrictFderivAt.congr_of_eventuallyEq (h : HasStrictFderivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) :
    HasStrictFderivAt f₁ f' x :=
  (h₁.has_strict_fderiv_at_iff fun _ => rfl).1 h
#align has_strict_fderiv_at.congr_of_eventually_eq HasStrictFderivAt.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasFderivAtFilter_iff (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x)
    (h₁ : ∀ x, f₀' x = f₁' x) : HasFderivAtFilter f₀ f₀' x L ↔ HasFderivAtFilter f₁ f₁' x L :=
  isO_congr (h₀.mono fun y hy => by simp only [hy, h₁, hx]) (eventually_of_forall fun _ => rfl)
#align filter.eventually_eq.has_fderiv_at_filter_iff Filter.EventuallyEq.hasFderivAtFilter_iff

theorem HasFderivAtFilter.congr_of_eventuallyEq (h : HasFderivAtFilter f f' x L) (hL : f₁ =ᶠ[L] f)
    (hx : f₁ x = f x) : HasFderivAtFilter f₁ f' x L :=
  (hL.has_fderiv_at_filter_iff hx fun _ => rfl).2 h
#align has_fderiv_at_filter.congr_of_eventually_eq HasFderivAtFilter.congr_of_eventuallyEq

theorem Filter.EventuallyEq.hasFderivAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    HasFderivAt f₀ f' x ↔ HasFderivAt f₁ f' x :=
  h.has_fderiv_at_filter_iff h.eq_of_nhds fun _ => rfl
#align filter.eventually_eq.has_fderiv_at_iff Filter.EventuallyEq.hasFderivAt_iff

theorem Filter.EventuallyEq.differentiableAt_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
    DifferentiableAt 𝕜 f₀ x ↔ DifferentiableAt 𝕜 f₁ x :=
  exists_congr fun f' => h.has_fderiv_at_iff
#align filter.eventually_eq.differentiable_at_iff Filter.EventuallyEq.differentiableAt_iff

theorem Filter.EventuallyEq.hasFderivWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    HasFderivWithinAt f₀ f' s x ↔ HasFderivWithinAt f₁ f' s x :=
  h.has_fderiv_at_filter_iff hx fun _ => rfl
#align filter.eventually_eq.has_fderiv_within_at_iff Filter.EventuallyEq.hasFderivWithinAt_iff

theorem Filter.EventuallyEq.hasFderivWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    HasFderivWithinAt f₀ f' s x ↔ HasFderivWithinAt f₁ f' s x :=
  h.has_fderiv_within_at_iff (h.eq_of_nhds_within hx)
#align filter.eventually_eq.has_fderiv_within_at_iff_of_mem Filter.EventuallyEq.hasFderivWithinAt_iff_of_mem

theorem Filter.EventuallyEq.differentiableWithinAt_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  exists_congr fun f' => h.has_fderiv_within_at_iff hx
#align filter.eventually_eq.differentiable_within_at_iff Filter.EventuallyEq.differentiableWithinAt_iff

theorem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
    DifferentiableWithinAt 𝕜 f₀ s x ↔ DifferentiableWithinAt 𝕜 f₁ s x :=
  h.differentiable_within_at_iff (h.eq_of_nhds_within hx)
#align filter.eventually_eq.differentiable_within_at_iff_of_mem Filter.EventuallyEq.differentiableWithinAt_iff_of_mem

theorem HasFderivWithinAt.congr_mono (h : HasFderivWithinAt f f' s x) (ht : ∀ x ∈ t, f₁ x = f x)
    (hx : f₁ x = f x) (h₁ : t ⊆ s) : HasFderivWithinAt f₁ f' t x :=
  HasFderivAtFilter.congr_of_eventuallyEq (h.mono h₁) (Filter.mem_inf_of_right ht) hx
#align has_fderiv_within_at.congr_mono HasFderivWithinAt.congr_mono

theorem HasFderivWithinAt.congr (h : HasFderivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : HasFderivWithinAt f₁ f' s x :=
  h.congr_mono hs hx (Subset.refl _)
#align has_fderiv_within_at.congr HasFderivWithinAt.congr

theorem HasFderivWithinAt.congr' (h : HasFderivWithinAt f f' s x) (hs : ∀ x ∈ s, f₁ x = f x)
    (hx : x ∈ s) : HasFderivWithinAt f₁ f' s x :=
  h.congr hs (hs x hx)
#align has_fderiv_within_at.congr' HasFderivWithinAt.congr'

theorem HasFderivWithinAt.congr_of_eventuallyEq (h : HasFderivWithinAt f f' s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : HasFderivWithinAt f₁ f' s x :=
  HasFderivAtFilter.congr_of_eventuallyEq h h₁ hx
#align has_fderiv_within_at.congr_of_eventually_eq HasFderivWithinAt.congr_of_eventuallyEq

theorem HasFderivAt.congr_of_eventuallyEq (h : HasFderivAt f f' x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
    HasFderivAt f₁ f' x :=
  HasFderivAtFilter.congr_of_eventuallyEq h h₁ (mem_of_mem_nhds h₁ : _)
#align has_fderiv_at.congr_of_eventually_eq HasFderivAt.congr_of_eventuallyEq

theorem DifferentiableWithinAt.congr_mono (h : DifferentiableWithinAt 𝕜 f s x)
    (ht : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (h₁ : t ⊆ s) : DifferentiableWithinAt 𝕜 f₁ t x :=
  (HasFderivWithinAt.congr_mono h.HasFderivWithinAt ht hx h₁).DifferentiableWithinAt
#align differentiable_within_at.congr_mono DifferentiableWithinAt.congr_mono

theorem DifferentiableWithinAt.congr (h : DifferentiableWithinAt 𝕜 f s x) (ht : ∀ x ∈ s, f₁ x = f x)
    (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  DifferentiableWithinAt.congr_mono h ht hx (Subset.refl _)
#align differentiable_within_at.congr DifferentiableWithinAt.congr

theorem DifferentiableWithinAt.congr_of_eventuallyEq (h : DifferentiableWithinAt 𝕜 f s x)
    (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : DifferentiableWithinAt 𝕜 f₁ s x :=
  (h.HasFderivWithinAt.congr_of_eventually_eq h₁ hx).DifferentiableWithinAt
#align differentiable_within_at.congr_of_eventually_eq DifferentiableWithinAt.congr_of_eventuallyEq

theorem DifferentiableOn.congr_mono (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ t, f₁ x = f x)
    (h₁ : t ⊆ s) : DifferentiableOn 𝕜 f₁ t := fun x hx => (h x (h₁ hx)).congr_mono h' (h' x hx) h₁
#align differentiable_on.congr_mono DifferentiableOn.congr_mono

theorem DifferentiableOn.congr (h : DifferentiableOn 𝕜 f s) (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s := fun x hx => (h x hx).congr h' (h' x hx)
#align differentiable_on.congr DifferentiableOn.congr

theorem differentiableOn_congr (h' : ∀ x ∈ s, f₁ x = f x) :
    DifferentiableOn 𝕜 f₁ s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => DifferentiableOn.congr h fun y hy => (h' y hy).symm, fun h =>
    DifferentiableOn.congr h h'⟩
#align differentiable_on_congr differentiableOn_congr

theorem DifferentiableAt.congr_of_eventuallyEq (h : DifferentiableAt 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
    DifferentiableAt 𝕜 f₁ x :=
  hL.differentiable_at_iff.2 h
#align differentiable_at.congr_of_eventually_eq DifferentiableAt.congr_of_eventuallyEq

theorem DifferentiableWithinAt.fderivWithin_congr_mono (h : DifferentiableWithinAt 𝕜 f s x)
    (hs : ∀ x ∈ t, f₁ x = f x) (hx : f₁ x = f x) (hxt : UniqueDiffWithinAt 𝕜 t x) (h₁ : t ⊆ s) :
    fderivWithin 𝕜 f₁ t x = fderivWithin 𝕜 f s x :=
  (HasFderivWithinAt.congr_mono h.HasFderivWithinAt hs hx h₁).fderivWithin hxt
#align differentiable_within_at.fderiv_within_congr_mono DifferentiableWithinAt.fderivWithin_congr_mono

theorem Filter.EventuallyEq.fderivWithin_eq (hs : UniqueDiffWithinAt 𝕜 s x) (hL : f₁ =ᶠ[𝓝[s] x] f)
    (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then
    HasFderivWithinAt.fderivWithin (h.HasFderivWithinAt.congr_of_eventually_eq hL hx) hs
  else
    by
    have h' : ¬DifferentiableWithinAt 𝕜 f₁ s x :=
      mt (fun h => h.congr_of_eventually_eq (hL.mono fun x => Eq.symm) hx.symm) h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt h']
#align filter.eventually_eq.fderiv_within_eq Filter.EventuallyEq.fderivWithin_eq

theorem Filter.EventuallyEq.fderivWithin_eq_nhds (hs : UniqueDiffWithinAt 𝕜 s x)
    (hL : f₁ =ᶠ[𝓝 x] f) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  (show f₁ =ᶠ[𝓝[s] x] f from nhdsWithin_le_nhds hL).fderiv_within_eq hs (mem_of_mem_nhds hL : _)
#align filter.eventually_eq.fderiv_within_eq_nhds Filter.EventuallyEq.fderivWithin_eq_nhds

theorem fderivWithin_congr (hs : UniqueDiffWithinAt 𝕜 s x) (hL : ∀ y ∈ s, f₁ y = f y)
    (hx : f₁ x = f x) : fderivWithin 𝕜 f₁ s x = fderivWithin 𝕜 f s x :=
  by
  apply Filter.EventuallyEq.fderivWithin_eq hs _ hx
  apply mem_of_superset self_mem_nhdsWithin
  exact hL
#align fderiv_within_congr fderivWithin_congr

theorem Filter.EventuallyEq.fderiv_eq (hL : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ x = fderiv 𝕜 f x :=
  by
  have A : f₁ x = f x := hL.eq_of_nhds
  rw [← fderivWithin_univ, ← fderivWithin_univ]
  rw [← nhdsWithin_univ] at hL
  exact hL.fderiv_within_eq uniqueDiffWithinAtUniv A
#align filter.eventually_eq.fderiv_eq Filter.EventuallyEq.fderiv_eq

protected theorem Filter.EventuallyEq.fderiv (h : f₁ =ᶠ[𝓝 x] f) : fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
  h.eventually_eq_nhds.mono fun x h => h.fderiv_eq
#align filter.eventually_eq.fderiv Filter.EventuallyEq.fderiv

end congr

section id

/-! ### Derivative of the identity -/


theorem hasStrictFderivAt_id (x : E) : HasStrictFderivAt id (id 𝕜 E) x :=
  (isO_zero _ _).congr_left <| by simp
#align has_strict_fderiv_at_id hasStrictFderivAt_id

theorem hasFderivAtFilter_id (x : E) (L : Filter E) : HasFderivAtFilter id (id 𝕜 E) x L :=
  (isO_zero _ _).congr_left <| by simp
#align has_fderiv_at_filter_id hasFderivAtFilter_id

theorem hasFderivWithinAt_id (x : E) (s : Set E) : HasFderivWithinAt id (id 𝕜 E) s x :=
  hasFderivAtFilter_id _ _
#align has_fderiv_within_at_id hasFderivWithinAt_id

theorem hasFderivAt_id (x : E) : HasFderivAt id (id 𝕜 E) x :=
  hasFderivAtFilter_id _ _
#align has_fderiv_at_id hasFderivAt_id

@[simp]
theorem differentiableAt_id : DifferentiableAt 𝕜 id x :=
  (hasFderivAt_id x).DifferentiableAt
#align differentiable_at_id differentiableAt_id

@[simp]
theorem differentiableAt_id' : DifferentiableAt 𝕜 (fun x => x) x :=
  (hasFderivAt_id x).DifferentiableAt
#align differentiable_at_id' differentiableAt_id'

theorem differentiableWithinAt_id : DifferentiableWithinAt 𝕜 id s x :=
  differentiableAt_id.DifferentiableWithinAt
#align differentiable_within_at_id differentiableWithinAt_id

@[simp]
theorem differentiable_id : Differentiable 𝕜 (id : E → E) := fun x => differentiableAt_id
#align differentiable_id differentiable_id

@[simp]
theorem differentiable_id' : Differentiable 𝕜 fun x : E => x := fun x => differentiableAt_id
#align differentiable_id' differentiable_id'

theorem differentiableOn_id : DifferentiableOn 𝕜 id s :=
  differentiable_id.DifferentiableOn
#align differentiable_on_id differentiableOn_id

theorem fderiv_id : fderiv 𝕜 id x = id 𝕜 E :=
  HasFderivAt.fderiv (hasFderivAt_id x)
#align fderiv_id fderiv_id

@[simp]
theorem fderiv_id' : fderiv 𝕜 (fun x : E => x) x = ContinuousLinearMap.id 𝕜 E :=
  fderiv_id
#align fderiv_id' fderiv_id'

theorem fderivWithin_id (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 id s x = id 𝕜 E :=
  by
  rw [DifferentiableAt.fderivWithin differentiableAt_id hxs]
  exact fderiv_id
#align fderiv_within_id fderivWithin_id

theorem fderivWithin_id' (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => x) s x = ContinuousLinearMap.id 𝕜 E :=
  fderivWithin_id hxs
#align fderiv_within_id' fderivWithin_id'

end id

section Const

/-! ### derivative of a constant function -/


theorem hasStrictFderivAt_const (c : F) (x : E) :
    HasStrictFderivAt (fun _ => c) (0 : E →L[𝕜] F) x :=
  (isO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_strict_fderiv_at_const hasStrictFderivAt_const

theorem hasFderivAtFilter_const (c : F) (x : E) (L : Filter E) :
    HasFderivAtFilter (fun x => c) (0 : E →L[𝕜] F) x L :=
  (isO_zero _ _).congr_left fun _ => by simp only [zero_apply, sub_self]
#align has_fderiv_at_filter_const hasFderivAtFilter_const

theorem hasFderivWithinAt_const (c : F) (x : E) (s : Set E) :
    HasFderivWithinAt (fun x => c) (0 : E →L[𝕜] F) s x :=
  hasFderivAtFilter_const _ _ _
#align has_fderiv_within_at_const hasFderivWithinAt_const

theorem hasFderivAt_const (c : F) (x : E) : HasFderivAt (fun x => c) (0 : E →L[𝕜] F) x :=
  hasFderivAtFilter_const _ _ _
#align has_fderiv_at_const hasFderivAt_const

@[simp]
theorem differentiableAt_const (c : F) : DifferentiableAt 𝕜 (fun x => c) x :=
  ⟨0, hasFderivAt_const c x⟩
#align differentiable_at_const differentiableAt_const

theorem differentiableWithinAt_const (c : F) : DifferentiableWithinAt 𝕜 (fun x => c) s x :=
  DifferentiableAt.differentiableWithinAt (differentiableAt_const _)
#align differentiable_within_at_const differentiableWithinAt_const

theorem fderiv_const_apply (c : F) : fderiv 𝕜 (fun y => c) x = 0 :=
  HasFderivAt.fderiv (hasFderivAt_const c x)
#align fderiv_const_apply fderiv_const_apply

@[simp]
theorem fderiv_const (c : F) : (fderiv 𝕜 fun y : E => c) = 0 :=
  by
  ext m
  rw [fderiv_const_apply]
  rfl
#align fderiv_const fderiv_const

theorem fderivWithin_const_apply (c : F) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => c) s x = 0 :=
  by
  rw [DifferentiableAt.fderivWithin (differentiableAt_const _) hxs]
  exact fderiv_const_apply _
#align fderiv_within_const_apply fderivWithin_const_apply

@[simp]
theorem differentiable_const (c : F) : Differentiable 𝕜 fun x : E => c := fun x =>
  differentiableAt_const _
#align differentiable_const differentiable_const

theorem differentiableOn_const (c : F) : DifferentiableOn 𝕜 (fun x => c) s :=
  (differentiable_const _).DifferentiableOn
#align differentiable_on_const differentiableOn_const

theorem hasFderivWithinAt_singleton (f : E → F) (x : E) :
    HasFderivWithinAt f (0 : E →L[𝕜] F) {x} x := by
  simp only [HasFderivWithinAt, nhdsWithin_singleton, HasFderivAtFilter, is_o_pure,
    ContinuousLinearMap.zero_apply, sub_self]
#align has_fderiv_within_at_singleton hasFderivWithinAt_singleton

theorem hasFderivAt_of_subsingleton [h : Subsingleton E] (f : E → F) (x : E) :
    HasFderivAt f (0 : E →L[𝕜] F) x :=
  by
  rw [← hasFderivWithinAt_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)]
  exact hasFderivWithinAt_singleton f x
#align has_fderiv_at_of_subsingleton hasFderivAt_of_subsingleton

theorem differentiableOn_empty : DifferentiableOn 𝕜 f ∅ := fun x => False.elim
#align differentiable_on_empty differentiableOn_empty

theorem differentiableOn_singleton : DifferentiableOn 𝕜 f {x} :=
  forall_eq.2 (hasFderivWithinAt_singleton f x).DifferentiableWithinAt
#align differentiable_on_singleton differentiableOn_singleton

theorem Set.Subsingleton.differentiableOn (hs : s.Subsingleton) : DifferentiableOn 𝕜 f s :=
  hs.inductionOn differentiableOn_empty fun x => differentiableOn_singleton
#align set.subsingleton.differentiable_on Set.Subsingleton.differentiableOn

theorem hasFderivAt_zero_of_eventually_const (c : F) (hf : f =ᶠ[𝓝 x] fun y => c) :
    HasFderivAt f (0 : E →L[𝕜] F) x :=
  (hasFderivAt_const _ _).congr_of_eventually_eq hf
#align has_fderiv_at_zero_of_eventually_const hasFderivAt_zero_of_eventually_const

end Const

section ContinuousLinearMap

/-!
### Continuous linear maps

There are currently two variants of these in mathlib, the bundled version
(named `continuous_linear_map`, and denoted `E →L[𝕜] F`), and the unbundled version (with a
predicate `is_bounded_linear_map`). We give statements for both versions. -/


protected theorem ContinuousLinearMap.hasStrictFderivAt {x : E} : HasStrictFderivAt e e x :=
  (isO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
#align continuous_linear_map.has_strict_fderiv_at ContinuousLinearMap.hasStrictFderivAt

protected theorem ContinuousLinearMap.hasFderivAtFilter : HasFderivAtFilter e e x L :=
  (isO_zero _ _).congr_left fun x => by simp only [e.map_sub, sub_self]
#align continuous_linear_map.has_fderiv_at_filter ContinuousLinearMap.hasFderivAtFilter

protected theorem ContinuousLinearMap.hasFderivWithinAt : HasFderivWithinAt e e s x :=
  e.HasFderivAtFilter
#align continuous_linear_map.has_fderiv_within_at ContinuousLinearMap.hasFderivWithinAt

protected theorem ContinuousLinearMap.hasFderivAt : HasFderivAt e e x :=
  e.HasFderivAtFilter
#align continuous_linear_map.has_fderiv_at ContinuousLinearMap.hasFderivAt

@[simp]
protected theorem ContinuousLinearMap.differentiableAt : DifferentiableAt 𝕜 e x :=
  e.HasFderivAt.DifferentiableAt
#align continuous_linear_map.differentiable_at ContinuousLinearMap.differentiableAt

protected theorem ContinuousLinearMap.differentiableWithinAt : DifferentiableWithinAt 𝕜 e s x :=
  e.DifferentiableAt.DifferentiableWithinAt
#align continuous_linear_map.differentiable_within_at ContinuousLinearMap.differentiableWithinAt

@[simp]
protected theorem ContinuousLinearMap.fderiv : fderiv 𝕜 e x = e :=
  e.HasFderivAt.fderiv
#align continuous_linear_map.fderiv ContinuousLinearMap.fderiv

protected theorem ContinuousLinearMap.fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 e s x = e :=
  by
  rw [DifferentiableAt.fderivWithin e.differentiable_at hxs]
  exact e.fderiv
#align continuous_linear_map.fderiv_within ContinuousLinearMap.fderivWithin

@[simp]
protected theorem ContinuousLinearMap.differentiable : Differentiable 𝕜 e := fun x =>
  e.DifferentiableAt
#align continuous_linear_map.differentiable ContinuousLinearMap.differentiable

protected theorem ContinuousLinearMap.differentiableOn : DifferentiableOn 𝕜 e s :=
  e.Differentiable.DifferentiableOn
#align continuous_linear_map.differentiable_on ContinuousLinearMap.differentiableOn

theorem IsBoundedLinearMap.hasFderivAtFilter (h : IsBoundedLinearMap 𝕜 f) :
    HasFderivAtFilter f h.toContinuousLinearMap x L :=
  h.toContinuousLinearMap.HasFderivAtFilter
#align is_bounded_linear_map.has_fderiv_at_filter IsBoundedLinearMap.hasFderivAtFilter

theorem IsBoundedLinearMap.hasFderivWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFderivWithinAt f h.toContinuousLinearMap s x :=
  h.HasFderivAtFilter
#align is_bounded_linear_map.has_fderiv_within_at IsBoundedLinearMap.hasFderivWithinAt

theorem IsBoundedLinearMap.hasFderivAt (h : IsBoundedLinearMap 𝕜 f) :
    HasFderivAt f h.toContinuousLinearMap x :=
  h.HasFderivAtFilter
#align is_bounded_linear_map.has_fderiv_at IsBoundedLinearMap.hasFderivAt

theorem IsBoundedLinearMap.differentiableAt (h : IsBoundedLinearMap 𝕜 f) : DifferentiableAt 𝕜 f x :=
  h.HasFderivAt.DifferentiableAt
#align is_bounded_linear_map.differentiable_at IsBoundedLinearMap.differentiableAt

theorem IsBoundedLinearMap.differentiableWithinAt (h : IsBoundedLinearMap 𝕜 f) :
    DifferentiableWithinAt 𝕜 f s x :=
  h.DifferentiableAt.DifferentiableWithinAt
#align is_bounded_linear_map.differentiable_within_at IsBoundedLinearMap.differentiableWithinAt

theorem IsBoundedLinearMap.fderiv (h : IsBoundedLinearMap 𝕜 f) :
    fderiv 𝕜 f x = h.toContinuousLinearMap :=
  HasFderivAt.fderiv h.HasFderivAt
#align is_bounded_linear_map.fderiv IsBoundedLinearMap.fderiv

theorem IsBoundedLinearMap.fderivWithin (h : IsBoundedLinearMap 𝕜 f)
    (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 f s x = h.toContinuousLinearMap :=
  by
  rw [DifferentiableAt.fderivWithin h.differentiable_at hxs]
  exact h.fderiv
#align is_bounded_linear_map.fderiv_within IsBoundedLinearMap.fderivWithin

theorem IsBoundedLinearMap.differentiable (h : IsBoundedLinearMap 𝕜 f) : Differentiable 𝕜 f :=
  fun x => h.DifferentiableAt
#align is_bounded_linear_map.differentiable IsBoundedLinearMap.differentiable

theorem IsBoundedLinearMap.differentiableOn (h : IsBoundedLinearMap 𝕜 f) : DifferentiableOn 𝕜 f s :=
  h.Differentiable.DifferentiableOn
#align is_bounded_linear_map.differentiable_on IsBoundedLinearMap.differentiableOn

end ContinuousLinearMap

section Composition

/-!
### Derivative of the composition of two functions

For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/


variable (x)

theorem HasFderivAtFilter.comp {g : F → G} {g' : F →L[𝕜] G} {L' : Filter F}
    (hg : HasFderivAtFilter g g' (f x) L') (hf : HasFderivAtFilter f f' x L) (hL : Tendsto f L L') :
    HasFderivAtFilter (g ∘ f) (g'.comp f') x L :=
  by
  let eq₁ := (g'.is_O_comp _ _).trans_is_o hf
  let eq₂ := (hg.comp_tendsto hL).trans_is_O hf.is_O_sub
  refine' eq₂.triangle (eq₁.congr_left fun x' => _)
  simp
#align has_fderiv_at_filter.comp HasFderivAtFilter.comp

/- A readable version of the previous theorem,
   a general form of the chain rule. -/
example {g : F → G} {g' : F →L[𝕜] G} (hg : HasFderivAtFilter g g' (f x) (L.map f))
    (hf : HasFderivAtFilter f f' x L) : HasFderivAtFilter (g ∘ f) (g'.comp f') x L :=
  by
  unfold HasFderivAtFilter at hg
  have :=
    calc
      (fun x' => g (f x') - g (f x) - g' (f x' - f x)) =o[L] fun x' => f x' - f x :=
        hg.comp_tendsto le_rfl
      _ =O[L] fun x' => x' - x := hf.is_O_sub
      
  refine' this.triangle _
  calc
    (fun x' : E => g' (f x' - f x) - g'.comp f' (x' - x)) =ᶠ[L] fun x' =>
        g' (f x' - f x - f' (x' - x)) :=
      eventually_of_forall fun x' => by simp
    _ =O[L] fun x' => f x' - f x - f' (x' - x) := g'.is_O_comp _ _
    _ =o[L] fun x' => x' - x := hf
    

theorem HasFderivWithinAt.comp {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFderivWithinAt g g' t (f x)) (hf : HasFderivWithinAt f f' s x) (hst : MapsTo f s t) :
    HasFderivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.comp x hf <| hf.ContinuousWithinAt.tendsto_nhds_within hst
#align has_fderiv_within_at.comp HasFderivWithinAt.comp

theorem HasFderivAt.comp_hasFderivWithinAt {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasFderivAt g g' (f x)) (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (g ∘ f) (g'.comp f') s x :=
  hg.comp x hf hf.ContinuousWithinAt
#align has_fderiv_at.comp_has_fderiv_within_at HasFderivAt.comp_hasFderivWithinAt

theorem HasFderivWithinAt.comp_of_mem {g : F → G} {g' : F →L[𝕜] G} {t : Set F}
    (hg : HasFderivWithinAt g g' t (f x)) (hf : HasFderivWithinAt f f' s x)
    (hst : Tendsto f (𝓝[s] x) (𝓝[t] f x)) : HasFderivWithinAt (g ∘ f) (g'.comp f') s x :=
  HasFderivAtFilter.comp x hg hf hst
#align has_fderiv_within_at.comp_of_mem HasFderivWithinAt.comp_of_mem

/-- The chain rule. -/
theorem HasFderivAt.comp {g : F → G} {g' : F →L[𝕜] G} (hg : HasFderivAt g g' (f x))
    (hf : HasFderivAt f f' x) : HasFderivAt (g ∘ f) (g'.comp f') x :=
  hg.comp x hf hf.ContinuousAt
#align has_fderiv_at.comp HasFderivAt.comp

theorem DifferentiableWithinAt.comp {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x)
    (h : MapsTo f s t) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  (hg.HasFderivWithinAt.comp x hf.HasFderivWithinAt h).DifferentiableWithinAt
#align differentiable_within_at.comp DifferentiableWithinAt.comp

theorem DifferentiableWithinAt.comp' {g : F → G} {t : Set F}
    (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (g ∘ f) (s ∩ f ⁻¹' t) x :=
  hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)
#align differentiable_within_at.comp' DifferentiableWithinAt.comp'

theorem DifferentiableAt.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (g ∘ f) x :=
  (hg.HasFderivAt.comp x hf.HasFderivAt).DifferentiableAt
#align differentiable_at.comp DifferentiableAt.comp

theorem DifferentiableAt.comp_differentiableWithinAt {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (g ∘ f) s x :=
  hg.DifferentiableWithinAt.comp x hf (mapsTo_univ _ _)
#align differentiable_at.comp_differentiable_within_at DifferentiableAt.comp_differentiableWithinAt

theorem fderivWithin.comp {g : F → G} {t : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (h : MapsTo f s t) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderivWithin 𝕜 g t (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.HasFderivWithinAt.comp x hf.HasFderivWithinAt h).fderivWithin hxs
#align fderiv_within.comp fderivWithin.comp

/-- Ternary version of `fderiv_within.comp`, with equality assumptions of basepoints added, in
  order to apply more easily as a rewrite from right-to-left. -/
theorem fderivWithin.comp₃ {g' : G → G'} {g : F → G} {t : Set F} {u : Set G} {y : F} {y' : G}
    (hg' : DifferentiableWithinAt 𝕜 g' u y') (hg : DifferentiableWithinAt 𝕜 g t y)
    (hf : DifferentiableWithinAt 𝕜 f s x) (h2g : MapsTo g t u) (h2f : MapsTo f s t) (h3g : g y = y')
    (h3f : f x = y) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g' ∘ g ∘ f) s x =
      (fderivWithin 𝕜 g' u y').comp ((fderivWithin 𝕜 g t y).comp (fderivWithin 𝕜 f s x)) :=
  by
  substs h3g h3f
  exact
    (hg'.has_fderiv_within_at.comp x (hg.has_fderiv_within_at.comp x hf.has_fderiv_within_at h2f) <|
          h2g.comp h2f).fderivWithin
      hxs
#align fderiv_within.comp₃ fderivWithin.comp₃

theorem fderiv.comp {g : F → G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (g ∘ f) x = (fderiv 𝕜 g (f x)).comp (fderiv 𝕜 f x) :=
  (hg.HasFderivAt.comp x hf.HasFderivAt).fderiv
#align fderiv.comp fderiv.comp

theorem fderiv.comp_fderivWithin {g : F → G} (hg : DifferentiableAt 𝕜 g (f x))
    (hf : DifferentiableWithinAt 𝕜 f s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (g ∘ f) s x = (fderiv 𝕜 g (f x)).comp (fderivWithin 𝕜 f s x) :=
  (hg.HasFderivAt.comp_has_fderiv_within_at x hf.HasFderivWithinAt).fderivWithin hxs
#align fderiv.comp_fderiv_within fderiv.comp_fderivWithin

theorem DifferentiableOn.comp {g : F → G} {t : Set F} (hg : DifferentiableOn 𝕜 g t)
    (hf : DifferentiableOn 𝕜 f s) (st : MapsTo f s t) : DifferentiableOn 𝕜 (g ∘ f) s := fun x hx =>
  DifferentiableWithinAt.comp x (hg (f x) (st hx)) (hf x hx) st
#align differentiable_on.comp DifferentiableOn.comp

theorem Differentiable.comp {g : F → G} (hg : Differentiable 𝕜 g) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 (g ∘ f) := fun x => DifferentiableAt.comp x (hg (f x)) (hf x)
#align differentiable.comp Differentiable.comp

theorem Differentiable.comp_differentiableOn {g : F → G} (hg : Differentiable 𝕜 g)
    (hf : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (g ∘ f) s :=
  hg.DifferentiableOn.comp hf (mapsTo_univ _ _)
#align differentiable.comp_differentiable_on Differentiable.comp_differentiableOn

/-- The chain rule for derivatives in the sense of strict differentiability. -/
protected theorem HasStrictFderivAt.comp {g : F → G} {g' : F →L[𝕜] G}
    (hg : HasStrictFderivAt g g' (f x)) (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => g (f x)) (g'.comp f') x :=
  ((hg.comp_tendsto (hf.ContinuousAt.prod_map' hf.ContinuousAt)).trans_is_O hf.is_O_sub).triangle <|
    by simpa only [g'.map_sub, f'.coe_comp'] using (g'.is_O_comp _ _).trans_is_o hf
#align has_strict_fderiv_at.comp HasStrictFderivAt.comp

protected theorem Differentiable.iterate {f : E → E} (hf : Differentiable 𝕜 f) (n : ℕ) :
    Differentiable 𝕜 (f^[n]) :=
  Nat.recOn n differentiable_id fun n ihn => ihn.comp hf
#align differentiable.iterate Differentiable.iterate

protected theorem DifferentiableOn.iterate {f : E → E} (hf : DifferentiableOn 𝕜 f s)
    (hs : MapsTo f s s) (n : ℕ) : DifferentiableOn 𝕜 (f^[n]) s :=
  Nat.recOn n differentiableOn_id fun n ihn => ihn.comp hf hs
#align differentiable_on.iterate DifferentiableOn.iterate

variable {x}

protected theorem HasFderivAtFilter.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFderivAtFilter f f' x L) (hL : Tendsto f L L) (hx : f x = x) (n : ℕ) :
    HasFderivAtFilter (f^[n]) (f' ^ n) x L :=
  by
  induction' n with n ihn
  · exact hasFderivAtFilter_id x L
  · rw [Function.iterate_succ, pow_succ']
    rw [← hx] at ihn
    exact ihn.comp x hf hL
#align has_fderiv_at_filter.iterate HasFderivAtFilter.iterate

protected theorem HasFderivAt.iterate {f : E → E} {f' : E →L[𝕜] E} (hf : HasFderivAt f f' x)
    (hx : f x = x) (n : ℕ) : HasFderivAt (f^[n]) (f' ^ n) x :=
  by
  refine' hf.iterate _ hx n
  convert hf.continuous_at
  exact hx.symm
#align has_fderiv_at.iterate HasFderivAt.iterate

protected theorem HasFderivWithinAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasFderivWithinAt f f' s x) (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) :
    HasFderivWithinAt (f^[n]) (f' ^ n) s x :=
  by
  refine' hf.iterate _ hx n
  convert tendsto_inf.2 ⟨hf.continuous_within_at, _⟩
  exacts[hx.symm, (tendsto_principal_principal.2 hs).mono_left inf_le_right]
#align has_fderiv_within_at.iterate HasFderivWithinAt.iterate

protected theorem HasStrictFderivAt.iterate {f : E → E} {f' : E →L[𝕜] E}
    (hf : HasStrictFderivAt f f' x) (hx : f x = x) (n : ℕ) : HasStrictFderivAt (f^[n]) (f' ^ n) x :=
  by
  induction' n with n ihn
  · exact hasStrictFderivAt_id x
  · rw [Function.iterate_succ, pow_succ']
    rw [← hx] at ihn
    exact ihn.comp x hf
#align has_strict_fderiv_at.iterate HasStrictFderivAt.iterate

protected theorem DifferentiableAt.iterate {f : E → E} (hf : DifferentiableAt 𝕜 f x) (hx : f x = x)
    (n : ℕ) : DifferentiableAt 𝕜 (f^[n]) x :=
  (hf.HasFderivAt.iterate hx n).DifferentiableAt
#align differentiable_at.iterate DifferentiableAt.iterate

protected theorem DifferentiableWithinAt.iterate {f : E → E} (hf : DifferentiableWithinAt 𝕜 f s x)
    (hx : f x = x) (hs : MapsTo f s s) (n : ℕ) : DifferentiableWithinAt 𝕜 (f^[n]) s x :=
  (hf.HasFderivWithinAt.iterate hx hs n).DifferentiableWithinAt
#align differentiable_within_at.iterate DifferentiableWithinAt.iterate

end Composition

section CartesianProduct

/-! ### Derivative of the cartesian product of two functions -/


section Prod

variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

protected theorem HasStrictFderivAt.prod (hf₁ : HasStrictFderivAt f₁ f₁' x)
    (hf₂ : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.prodLeft hf₂
#align has_strict_fderiv_at.prod HasStrictFderivAt.prod

theorem HasFderivAtFilter.prod (hf₁ : HasFderivAtFilter f₁ f₁' x L)
    (hf₂ : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x L :=
  hf₁.prodLeft hf₂
#align has_fderiv_at_filter.prod HasFderivAtFilter.prod

theorem HasFderivWithinAt.prod (hf₁ : HasFderivWithinAt f₁ f₁' s x)
    (hf₂ : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') s x :=
  hf₁.Prod hf₂
#align has_fderiv_within_at.prod HasFderivWithinAt.prod

theorem HasFderivAt.prod (hf₁ : HasFderivAt f₁ f₁' x) (hf₂ : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₁ x, f₂ x)) (f₁'.Prod f₂') x :=
  hf₁.Prod hf₂
#align has_fderiv_at.prod HasFderivAt.prod

theorem hasFderivAt_prod_mk_left (e₀ : E) (f₀ : F) :
    HasFderivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  (hasFderivAt_id e₀).Prod (hasFderivAt_const f₀ e₀)
#align has_fderiv_at_prod_mk_left hasFderivAt_prod_mk_left

theorem hasFderivAt_prod_mk_right (e₀ : E) (f₀ : F) :
    HasFderivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  (hasFderivAt_const e₀ f₀).Prod (hasFderivAt_id f₀)
#align has_fderiv_at_prod_mk_right hasFderivAt_prod_mk_right

theorem DifferentiableWithinAt.prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.HasFderivWithinAt.Prod hf₂.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.prod DifferentiableWithinAt.prod

@[simp]
theorem DifferentiableAt.prod (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.HasFderivAt.Prod hf₂.HasFderivAt).DifferentiableAt
#align differentiable_at.prod DifferentiableAt.prod

theorem DifferentiableOn.prod (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx =>
  DifferentiableWithinAt.prod (hf₁ x hx) (hf₂ x hx)
#align differentiable_on.prod DifferentiableOn.prod

@[simp]
theorem Differentiable.prod (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x => DifferentiableAt.prod (hf₁ x) (hf₂ x)
#align differentiable.prod Differentiable.prod

theorem DifferentiableAt.fderiv_prod (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).Prod (fderiv 𝕜 f₂ x) :=
  (hf₁.HasFderivAt.Prod hf₂.HasFderivAt).fderiv
#align differentiable_at.fderiv_prod DifferentiableAt.fderiv_prod

theorem DifferentiableAt.fderivWithin_prod (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).Prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.HasFderivWithinAt.Prod hf₂.HasFderivWithinAt).fderivWithin hxs
#align differentiable_at.fderiv_within_prod DifferentiableAt.fderivWithin_prod

end Prod

section Fst

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

theorem hasStrictFderivAt_fst : HasStrictFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).HasStrictFderivAt
#align has_strict_fderiv_at_fst hasStrictFderivAt_fst

protected theorem HasStrictFderivAt.fst (h : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  hasStrictFderivAt_fst.comp x h
#align has_strict_fderiv_at.fst HasStrictFderivAt.fst

theorem hasFderivAtFilter_fst {L : Filter (E × F)} :
    HasFderivAtFilter (@Prod.fst E F) (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).HasFderivAtFilter
#align has_fderiv_at_filter_fst hasFderivAtFilter_fst

protected theorem HasFderivAtFilter.fst (h : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  hasFderivAtFilter_fst.comp x h tendsto_map
#align has_fderiv_at_filter.fst HasFderivAtFilter.fst

theorem hasFderivAt_fst : HasFderivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFderivAtFilter_fst
#align has_fderiv_at_fst hasFderivAt_fst

protected theorem HasFderivAt.fst (h : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  h.fst
#align has_fderiv_at.fst HasFderivAt.fst

theorem hasFderivWithinAt_fst {s : Set (E × F)} :
    HasFderivWithinAt (@Prod.fst E F) (fst 𝕜 E F) s p :=
  hasFderivAtFilter_fst
#align has_fderiv_within_at_fst hasFderivWithinAt_fst

protected theorem HasFderivWithinAt.fst (h : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  h.fst
#align has_fderiv_within_at.fst HasFderivWithinAt.fst

theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFderivAt_fst.DifferentiableAt
#align differentiable_at_fst differentiableAt_fst

@[simp]
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  differentiableAt_fst.comp x h
#align differentiable_at.fst DifferentiableAt.fst

theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun x =>
  differentiableAt_fst
#align differentiable_fst differentiable_fst

@[simp]
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  differentiable_fst.comp h
#align differentiable.fst Differentiable.fst

theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.DifferentiableWithinAt
#align differentiable_within_at_fst differentiableWithinAt_fst

protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  differentiableAt_fst.comp_differentiable_within_at x h
#align differentiable_within_at.fst DifferentiableWithinAt.fst

theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.DifferentiableOn
#align differentiable_on_fst differentiableOn_fst

protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  differentiable_fst.comp_differentiable_on h
#align differentiable_on.fst DifferentiableOn.fst

theorem fderiv_fst : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFderivAt_fst.fderiv
#align fderiv_fst fderiv_fst

theorem fderiv.fst (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFderivAt.fst.fderiv
#align fderiv.fst fderiv.fst

theorem fderivWithin_fst {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFderivWithinAt_fst.fderivWithin hs
#align fderiv_within_fst fderivWithin_fst

theorem fderivWithin.fst (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFderivWithinAt.fst.fderivWithin hs
#align fderiv_within.fst fderivWithin.fst

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

theorem hasStrictFderivAt_snd : HasStrictFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).HasStrictFderivAt
#align has_strict_fderiv_at_snd hasStrictFderivAt_snd

protected theorem HasStrictFderivAt.snd (h : HasStrictFderivAt f₂ f₂' x) :
    HasStrictFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  hasStrictFderivAt_snd.comp x h
#align has_strict_fderiv_at.snd HasStrictFderivAt.snd

theorem hasFderivAtFilter_snd {L : Filter (E × F)} :
    HasFderivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).HasFderivAtFilter
#align has_fderiv_at_filter_snd hasFderivAtFilter_snd

protected theorem HasFderivAtFilter.snd (h : HasFderivAtFilter f₂ f₂' x L) :
    HasFderivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  hasFderivAtFilter_snd.comp x h tendsto_map
#align has_fderiv_at_filter.snd HasFderivAtFilter.snd

theorem hasFderivAt_snd : HasFderivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFderivAtFilter_snd
#align has_fderiv_at_snd hasFderivAt_snd

protected theorem HasFderivAt.snd (h : HasFderivAt f₂ f₂' x) :
    HasFderivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd
#align has_fderiv_at.snd HasFderivAt.snd

theorem hasFderivWithinAt_snd {s : Set (E × F)} :
    HasFderivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFderivAtFilter_snd
#align has_fderiv_within_at_snd hasFderivWithinAt_snd

protected theorem HasFderivWithinAt.snd (h : HasFderivWithinAt f₂ f₂' s x) :
    HasFderivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd
#align has_fderiv_within_at.snd HasFderivWithinAt.snd

theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFderivAt_snd.DifferentiableAt
#align differentiable_at_snd differentiableAt_snd

@[simp]
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h
#align differentiable_at.snd DifferentiableAt.snd

theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun x =>
  differentiableAt_snd
#align differentiable_snd differentiable_snd

@[simp]
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h
#align differentiable.snd Differentiable.snd

theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.DifferentiableWithinAt
#align differentiable_within_at_snd differentiableWithinAt_snd

protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiable_within_at x h
#align differentiable_within_at.snd DifferentiableWithinAt.snd

theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.DifferentiableOn
#align differentiable_on_snd differentiableOn_snd

protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiable_on h
#align differentiable_on.snd DifferentiableOn.snd

theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFderivAt_snd.fderiv
#align fderiv_snd fderiv_snd

theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.HasFderivAt.snd.fderiv
#align fderiv.snd fderiv.snd

theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFderivWithinAt_snd.fderivWithin hs
#align fderiv_within_snd fderivWithin_snd

theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.HasFderivWithinAt.snd.fderivWithin hs
#align fderiv_within.snd fderivWithin.snd

end Snd

section Prod_map

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

protected theorem HasStrictFderivAt.prodMap (hf : HasStrictFderivAt f f' p.1)
    (hf₂ : HasStrictFderivAt f₂ f₂' p.2) : HasStrictFderivAt (Prod.map f f₂) (f'.prod_map f₂') p :=
  (hf.comp p hasStrictFderivAt_fst).Prod (hf₂.comp p hasStrictFderivAt_snd)
#align has_strict_fderiv_at.prod_map HasStrictFderivAt.prodMap

protected theorem HasFderivAt.prodMap (hf : HasFderivAt f f' p.1) (hf₂ : HasFderivAt f₂ f₂' p.2) :
    HasFderivAt (Prod.map f f₂) (f'.prod_map f₂') p :=
  (hf.comp p hasFderivAt_fst).Prod (hf₂.comp p hasFderivAt_snd)
#align has_fderiv_at.prod_map HasFderivAt.prodMap

@[simp]
protected theorem DifferentiableAt.prod_map (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).Prod (hf₂.comp p differentiableAt_snd)
#align differentiable_at.prod_map DifferentiableAt.prod_map

end Prod_map

end CartesianProduct

section ConstSmul

variable {R : Type _} [Semiring R] [Module R F] [SMulCommClass 𝕜 R F] [HasContinuousConstSmul R F]

/-! ### Derivative of a function multiplied by a constant -/


theorem HasStrictFderivAt.const_smul (h : HasStrictFderivAt f f' x) (c : R) :
    HasStrictFderivAt (fun x => c • f x) (c • f') x :=
  (c • (1 : F →L[𝕜] F)).HasStrictFderivAt.comp x h
#align has_strict_fderiv_at.const_smul HasStrictFderivAt.const_smul

theorem HasFderivAtFilter.const_smul (h : HasFderivAtFilter f f' x L) (c : R) :
    HasFderivAtFilter (fun x => c • f x) (c • f') x L :=
  (c • (1 : F →L[𝕜] F)).HasFderivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.const_smul HasFderivAtFilter.const_smul

theorem HasFderivWithinAt.const_smul (h : HasFderivWithinAt f f' s x) (c : R) :
    HasFderivWithinAt (fun x => c • f x) (c • f') s x :=
  h.const_smul c
#align has_fderiv_within_at.const_smul HasFderivWithinAt.const_smul

theorem HasFderivAt.const_smul (h : HasFderivAt f f' x) (c : R) :
    HasFderivAt (fun x => c • f x) (c • f') x :=
  h.const_smul c
#align has_fderiv_at.const_smul HasFderivAt.const_smul

theorem DifferentiableWithinAt.const_smul (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    DifferentiableWithinAt 𝕜 (fun y => c • f y) s x :=
  (h.HasFderivWithinAt.const_smul c).DifferentiableWithinAt
#align differentiable_within_at.const_smul DifferentiableWithinAt.const_smul

theorem DifferentiableAt.const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    DifferentiableAt 𝕜 (fun y => c • f y) x :=
  (h.HasFderivAt.const_smul c).DifferentiableAt
#align differentiable_at.const_smul DifferentiableAt.const_smul

theorem DifferentiableOn.const_smul (h : DifferentiableOn 𝕜 f s) (c : R) :
    DifferentiableOn 𝕜 (fun y => c • f y) s := fun x hx => (h x hx).const_smul c
#align differentiable_on.const_smul DifferentiableOn.const_smul

theorem Differentiable.const_smul (h : Differentiable 𝕜 f) (c : R) :
    Differentiable 𝕜 fun y => c • f y := fun x => (h x).const_smul c
#align differentiable.const_smul Differentiable.const_smul

theorem fderivWithin_const_smul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f s x) (c : R) :
    fderivWithin 𝕜 (fun y => c • f y) s x = c • fderivWithin 𝕜 f s x :=
  (h.HasFderivWithinAt.const_smul c).fderivWithin hxs
#align fderiv_within_const_smul fderivWithin_const_smul

theorem fderiv_const_smul (h : DifferentiableAt 𝕜 f x) (c : R) :
    fderiv 𝕜 (fun y => c • f y) x = c • fderiv 𝕜 f x :=
  (h.HasFderivAt.const_smul c).fderiv
#align fderiv_const_smul fderiv_const_smul

end ConstSmul

section Add

/-! ### Derivative of the sum of two functions -/


theorem HasStrictFderivAt.add (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun y => f y + g y) (f' + g') x :=
  (hf.add hg).congr_left fun y =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_strict_fderiv_at.add HasStrictFderivAt.add

theorem HasFderivAtFilter.add (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
    HasFderivAtFilter (fun y => f y + g y) (f' + g') x L :=
  (hf.add hg).congr_left fun _ =>
    by
    simp only [LinearMap.sub_apply, LinearMap.add_apply, map_sub, map_add, add_apply]
    abel
#align has_fderiv_at_filter.add HasFderivAtFilter.add

theorem HasFderivWithinAt.add (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun y => f y + g y) (f' + g') s x :=
  hf.add hg
#align has_fderiv_within_at.add HasFderivWithinAt.add

theorem HasFderivAt.add (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun x => f x + g x) (f' + g') x :=
  hf.add hg
#align has_fderiv_at.add HasFderivAt.add

theorem DifferentiableWithinAt.add (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y + g y) s x :=
  (hf.HasFderivWithinAt.add hg.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.add DifferentiableWithinAt.add

@[simp]
theorem DifferentiableAt.add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y + g y) x :=
  (hf.HasFderivAt.add hg.HasFderivAt).DifferentiableAt
#align differentiable_at.add DifferentiableAt.add

theorem DifferentiableOn.add (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y + g y) s := fun x hx => (hf x hx).add (hg x hx)
#align differentiable_on.add DifferentiableOn.add

@[simp]
theorem Differentiable.add (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y + g y := fun x => (hf x).add (hg x)
#align differentiable.add Differentiable.add

theorem fderivWithin_add (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y + g y) s x = fderivWithin 𝕜 f s x + fderivWithin 𝕜 g s x :=
  (hf.HasFderivWithinAt.add hg.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_add fderivWithin_add

theorem fderiv_add (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y + g y) x = fderiv 𝕜 f x + fderiv 𝕜 g x :=
  (hf.HasFderivAt.add hg.HasFderivAt).fderiv
#align fderiv_add fderiv_add

theorem HasStrictFderivAt.add_const (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun y => f y + c) f' x :=
  add_zero f' ▸ hf.add (hasStrictFderivAt_const _ _)
#align has_strict_fderiv_at.add_const HasStrictFderivAt.add_const

theorem HasFderivAtFilter.add_const (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun y => f y + c) f' x L :=
  add_zero f' ▸ hf.add (hasFderivAtFilter_const _ _ _)
#align has_fderiv_at_filter.add_const HasFderivAtFilter.add_const

theorem HasFderivWithinAt.add_const (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun y => f y + c) f' s x :=
  hf.AddConst c
#align has_fderiv_within_at.add_const HasFderivWithinAt.add_const

theorem HasFderivAt.add_const (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => f x + c) f' x :=
  hf.AddConst c
#align has_fderiv_at.add_const HasFderivAt.add_const

theorem DifferentiableWithinAt.add_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x :=
  (hf.HasFderivWithinAt.AddConst c).DifferentiableWithinAt
#align differentiable_within_at.add_const DifferentiableWithinAt.add_const

@[simp]
theorem differentiableWithinAt_add_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y + c) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_within_at_add_const_iff differentiableWithinAt_add_const_iff

theorem DifferentiableAt.add_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x :=
  (hf.HasFderivAt.AddConst c).DifferentiableAt
#align differentiable_at.add_const DifferentiableAt.add_const

@[simp]
theorem differentiableAt_add_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y + c) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_at_add_const_iff differentiableAt_add_const_iff

theorem DifferentiableOn.add_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s := fun x hx => (hf x hx).AddConst c
#align differentiable_on.add_const DifferentiableOn.add_const

@[simp]
theorem differentiableOn_add_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y + c) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_on_add_const_iff differentiableOn_add_const_iff

theorem Differentiable.add_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y + c := fun x => (hf x).AddConst c
#align differentiable.add_const Differentiable.add_const

@[simp]
theorem differentiable_add_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y + c) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.add_const (-c), fun h => h.AddConst c⟩
#align differentiable_add_const_iff differentiable_add_const_iff

theorem fderivWithin_add_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y + c) s x = fderivWithin 𝕜 f s x :=
  if hf : DifferentiableWithinAt 𝕜 f s x then (hf.HasFderivWithinAt.AddConst c).fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt hf,
      fderivWithin_zero_of_not_differentiableWithinAt]
    simpa
#align fderiv_within_add_const fderivWithin_add_const

theorem fderiv_add_const (c : F) : fderiv 𝕜 (fun y => f y + c) x = fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_add_const uniqueDiffWithinAtUniv]
#align fderiv_add_const fderiv_add_const

theorem HasStrictFderivAt.const_add (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun y => c + f y) f' x :=
  zero_add f' ▸ (hasStrictFderivAt_const _ _).add hf
#align has_strict_fderiv_at.const_add HasStrictFderivAt.const_add

theorem HasFderivAtFilter.const_add (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun y => c + f y) f' x L :=
  zero_add f' ▸ (hasFderivAtFilter_const _ _ _).add hf
#align has_fderiv_at_filter.const_add HasFderivAtFilter.const_add

theorem HasFderivWithinAt.const_add (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun y => c + f y) f' s x :=
  hf.const_add c
#align has_fderiv_within_at.const_add HasFderivWithinAt.const_add

theorem HasFderivAt.const_add (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => c + f x) f' x :=
  hf.const_add c
#align has_fderiv_at.const_add HasFderivAt.const_add

theorem DifferentiableWithinAt.const_add (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x :=
  (hf.HasFderivWithinAt.const_add c).DifferentiableWithinAt
#align differentiable_within_at.const_add DifferentiableWithinAt.const_add

@[simp]
theorem differentiableWithinAt_const_add_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c + f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_within_at_const_add_iff differentiableWithinAt_const_add_iff

theorem DifferentiableAt.const_add (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x :=
  (hf.HasFderivAt.const_add c).DifferentiableAt
#align differentiable_at.const_add DifferentiableAt.const_add

@[simp]
theorem differentiableAt_const_add_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c + f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_at_const_add_iff differentiableAt_const_add_iff

theorem DifferentiableOn.const_add (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s := fun x hx => (hf x hx).const_add c
#align differentiable_on.const_add DifferentiableOn.const_add

@[simp]
theorem differentiableOn_const_add_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c + f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_on_const_add_iff differentiableOn_const_add_iff

theorem Differentiable.const_add (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c + f y := fun x => (hf x).const_add c
#align differentiable.const_add Differentiable.const_add

@[simp]
theorem differentiable_const_add_iff (c : F) :
    (Differentiable 𝕜 fun y => c + f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa using h.const_add (-c), fun h => h.const_add c⟩
#align differentiable_const_add_iff differentiable_const_add_iff

theorem fderivWithin_const_add (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c + f y) s x = fderivWithin 𝕜 f s x := by
  simpa only [add_comm] using fderivWithin_add_const hxs c
#align fderiv_within_const_add fderivWithin_const_add

theorem fderiv_const_add (c : F) : fderiv 𝕜 (fun y => c + f y) x = fderiv 𝕜 f x := by
  simp only [add_comm c, fderiv_add_const]
#align fderiv_const_add fderiv_const_add

end Add

section Sum

/-! ### Derivative of a finite sum of functions -/


open BigOperators

variable {ι : Type _} {u : Finset ι} {A : ι → E → F} {A' : ι → E →L[𝕜] F}

theorem HasStrictFderivAt.sum (h : ∀ i ∈ u, HasStrictFderivAt (A i) (A' i) x) :
    HasStrictFderivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  by
  dsimp [HasStrictFderivAt] at *
  convert is_o.sum h
  simp [Finset.sum_sub_distrib, ContinuousLinearMap.sum_apply]
#align has_strict_fderiv_at.sum HasStrictFderivAt.sum

theorem HasFderivAtFilter.sum (h : ∀ i ∈ u, HasFderivAtFilter (A i) (A' i) x L) :
    HasFderivAtFilter (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x L :=
  by
  dsimp [HasFderivAtFilter] at *
  convert is_o.sum h
  simp [ContinuousLinearMap.sum_apply]
#align has_fderiv_at_filter.sum HasFderivAtFilter.sum

theorem HasFderivWithinAt.sum (h : ∀ i ∈ u, HasFderivWithinAt (A i) (A' i) s x) :
    HasFderivWithinAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) s x :=
  HasFderivAtFilter.sum h
#align has_fderiv_within_at.sum HasFderivWithinAt.sum

theorem HasFderivAt.sum (h : ∀ i ∈ u, HasFderivAt (A i) (A' i) x) :
    HasFderivAt (fun y => ∑ i in u, A i y) (∑ i in u, A' i) x :=
  HasFderivAtFilter.sum h
#align has_fderiv_at.sum HasFderivAt.sum

theorem DifferentiableWithinAt.sum (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    DifferentiableWithinAt 𝕜 (fun y => ∑ i in u, A i y) s x :=
  HasFderivWithinAt.differentiableWithinAt <|
    HasFderivWithinAt.sum fun i hi => (h i hi).HasFderivWithinAt
#align differentiable_within_at.sum DifferentiableWithinAt.sum

@[simp]
theorem DifferentiableAt.sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    DifferentiableAt 𝕜 (fun y => ∑ i in u, A i y) x :=
  HasFderivAt.differentiableAt <| HasFderivAt.sum fun i hi => (h i hi).HasFderivAt
#align differentiable_at.sum DifferentiableAt.sum

theorem DifferentiableOn.sum (h : ∀ i ∈ u, DifferentiableOn 𝕜 (A i) s) :
    DifferentiableOn 𝕜 (fun y => ∑ i in u, A i y) s := fun x hx =>
  DifferentiableWithinAt.sum fun i hi => h i hi x hx
#align differentiable_on.sum DifferentiableOn.sum

@[simp]
theorem Differentiable.sum (h : ∀ i ∈ u, Differentiable 𝕜 (A i)) :
    Differentiable 𝕜 fun y => ∑ i in u, A i y := fun x => DifferentiableAt.sum fun i hi => h i hi x
#align differentiable.sum Differentiable.sum

theorem fderivWithin_sum (hxs : UniqueDiffWithinAt 𝕜 s x)
    (h : ∀ i ∈ u, DifferentiableWithinAt 𝕜 (A i) s x) :
    fderivWithin 𝕜 (fun y => ∑ i in u, A i y) s x = ∑ i in u, fderivWithin 𝕜 (A i) s x :=
  (HasFderivWithinAt.sum fun i hi => (h i hi).HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_sum fderivWithin_sum

theorem fderiv_sum (h : ∀ i ∈ u, DifferentiableAt 𝕜 (A i) x) :
    fderiv 𝕜 (fun y => ∑ i in u, A i y) x = ∑ i in u, fderiv 𝕜 (A i) x :=
  (HasFderivAt.sum fun i hi => (h i hi).HasFderivAt).fderiv
#align fderiv_sum fderiv_sum

end Sum

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has_*fderiv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `λ x i, φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `λ x, Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type _} [Fintype ι] {F' : ι → Type _} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
theorem hasStrictFderivAt_pi' :
    HasStrictFderivAt Φ Φ' x ↔ ∀ i, HasStrictFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  by
  simp only [HasStrictFderivAt, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_strict_fderiv_at_pi' hasStrictFderivAt_pi'

@[simp]
theorem hasStrictFderivAt_pi :
    HasStrictFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFderivAt (φ i) (φ' i) x :=
  hasStrictFderivAt_pi'
#align has_strict_fderiv_at_pi hasStrictFderivAt_pi

@[simp]
theorem hasFderivAtFilter_pi' :
    HasFderivAtFilter Φ Φ' x L ↔ ∀ i, HasFderivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L :=
  by
  simp only [HasFderivAtFilter, ContinuousLinearMap.coe_pi]
  exact is_o_pi
#align has_fderiv_at_filter_pi' hasFderivAtFilter_pi'

theorem hasFderivAtFilter_pi :
    HasFderivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔
      ∀ i, HasFderivAtFilter (φ i) (φ' i) x L :=
  hasFderivAtFilter_pi'
#align has_fderiv_at_filter_pi hasFderivAtFilter_pi

@[simp]
theorem hasFderivAt_pi' :
    HasFderivAt Φ Φ' x ↔ ∀ i, HasFderivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFderivAtFilter_pi'
#align has_fderiv_at_pi' hasFderivAt_pi'

theorem hasFderivAt_pi :
    HasFderivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFderivAt (φ i) (φ' i) x :=
  hasFderivAtFilter_pi
#align has_fderiv_at_pi hasFderivAt_pi

@[simp]
theorem hasFderivWithinAt_pi' :
    HasFderivWithinAt Φ Φ' s x ↔ ∀ i, HasFderivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFderivAtFilter_pi'
#align has_fderiv_within_at_pi' hasFderivWithinAt_pi'

theorem hasFderivWithinAt_pi :
    HasFderivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFderivWithinAt (φ i) (φ' i) s x :=
  hasFderivAtFilter_pi
#align has_fderiv_within_at_pi hasFderivWithinAt_pi

@[simp]
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  ⟨fun h i => (hasFderivWithinAt_pi'.1 h.HasFderivWithinAt i).DifferentiableWithinAt, fun h =>
    (hasFderivWithinAt_pi.2 fun i => (h i).HasFderivWithinAt).DifferentiableWithinAt⟩
#align differentiable_within_at_pi differentiableWithinAt_pi

@[simp]
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  ⟨fun h i => (hasFderivAt_pi'.1 h.HasFderivAt i).DifferentiableAt, fun h =>
    (hasFderivAt_pi.2 fun i => (h i).HasFderivAt).DifferentiableAt⟩
#align differentiable_at_pi differentiableAt_pi

theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩
#align differentiable_on_pi differentiableOn_pi

theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩
#align differentiable_pi differentiable_pi

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  (hasFderivWithinAt_pi.2 fun i => (h i).HasFderivWithinAt).fderivWithin hs
#align fderiv_within_pi fderivWithin_pi

theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  (hasFderivAt_pi.2 fun i => (h i).HasFderivAt).fderiv
#align fderiv_pi fderiv_pi

end Pi

section Neg

/-! ### Derivative of the negative of a function -/


theorem HasStrictFderivAt.neg (h : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun x => -f x) (-f') x :=
  (-1 : F →L[𝕜] F).HasStrictFderivAt.comp x h
#align has_strict_fderiv_at.neg HasStrictFderivAt.neg

theorem HasFderivAtFilter.neg (h : HasFderivAtFilter f f' x L) :
    HasFderivAtFilter (fun x => -f x) (-f') x L :=
  (-1 : F →L[𝕜] F).HasFderivAtFilter.comp x h tendsto_map
#align has_fderiv_at_filter.neg HasFderivAtFilter.neg

theorem HasFderivWithinAt.neg (h : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun x => -f x) (-f') s x :=
  h.neg
#align has_fderiv_within_at.neg HasFderivWithinAt.neg

theorem HasFderivAt.neg (h : HasFderivAt f f' x) : HasFderivAt (fun x => -f x) (-f') x :=
  h.neg
#align has_fderiv_at.neg HasFderivAt.neg

theorem DifferentiableWithinAt.neg (h : DifferentiableWithinAt 𝕜 f s x) :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x :=
  h.HasFderivWithinAt.neg.DifferentiableWithinAt
#align differentiable_within_at.neg DifferentiableWithinAt.neg

@[simp]
theorem differentiableWithinAt_neg_iff :
    DifferentiableWithinAt 𝕜 (fun y => -f y) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_within_at_neg_iff differentiableWithinAt_neg_iff

theorem DifferentiableAt.neg (h : DifferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (fun y => -f y) x :=
  h.HasFderivAt.neg.DifferentiableAt
#align differentiable_at.neg DifferentiableAt.neg

@[simp]
theorem differentiableAt_neg_iff : DifferentiableAt 𝕜 (fun y => -f y) x ↔ DifferentiableAt 𝕜 f x :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_at_neg_iff differentiableAt_neg_iff

theorem DifferentiableOn.neg (h : DifferentiableOn 𝕜 f s) : DifferentiableOn 𝕜 (fun y => -f y) s :=
  fun x hx => (h x hx).neg
#align differentiable_on.neg DifferentiableOn.neg

@[simp]
theorem differentiableOn_neg_iff : DifferentiableOn 𝕜 (fun y => -f y) s ↔ DifferentiableOn 𝕜 f s :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_on_neg_iff differentiableOn_neg_iff

theorem Differentiable.neg (h : Differentiable 𝕜 f) : Differentiable 𝕜 fun y => -f y := fun x =>
  (h x).neg
#align differentiable.neg Differentiable.neg

@[simp]
theorem differentiable_neg_iff : (Differentiable 𝕜 fun y => -f y) ↔ Differentiable 𝕜 f :=
  ⟨fun h => by simpa only [neg_neg] using h.neg, fun h => h.neg⟩
#align differentiable_neg_iff differentiable_neg_iff

theorem fderivWithin_neg (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun y => -f y) s x = -fderivWithin 𝕜 f s x :=
  if h : DifferentiableWithinAt 𝕜 f s x then h.HasFderivWithinAt.neg.fderivWithin hxs
  else
    by
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt, neg_zero]
    simpa
#align fderiv_within_neg fderivWithin_neg

@[simp]
theorem fderiv_neg : fderiv 𝕜 (fun y => -f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_neg uniqueDiffWithinAtUniv]
#align fderiv_neg fderiv_neg

end Neg

section Sub

/-! ### Derivative of the difference of two functions -/


theorem HasStrictFderivAt.sub (hf : HasStrictFderivAt f f' x) (hg : HasStrictFderivAt g g' x) :
    HasStrictFderivAt (fun x => f x - g x) (f' - g') x := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_strict_fderiv_at.sub HasStrictFderivAt.sub

theorem HasFderivAtFilter.sub (hf : HasFderivAtFilter f f' x L) (hg : HasFderivAtFilter g g' x L) :
    HasFderivAtFilter (fun x => f x - g x) (f' - g') x L := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg
#align has_fderiv_at_filter.sub HasFderivAtFilter.sub

theorem HasFderivWithinAt.sub (hf : HasFderivWithinAt f f' s x) (hg : HasFderivWithinAt g g' s x) :
    HasFderivWithinAt (fun x => f x - g x) (f' - g') s x :=
  hf.sub hg
#align has_fderiv_within_at.sub HasFderivWithinAt.sub

theorem HasFderivAt.sub (hf : HasFderivAt f f' x) (hg : HasFderivAt g g' x) :
    HasFderivAt (fun x => f x - g x) (f' - g') x :=
  hf.sub hg
#align has_fderiv_at.sub HasFderivAt.sub

theorem DifferentiableWithinAt.sub (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) : DifferentiableWithinAt 𝕜 (fun y => f y - g y) s x :=
  (hf.HasFderivWithinAt.sub hg.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.sub DifferentiableWithinAt.sub

@[simp]
theorem DifferentiableAt.sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    DifferentiableAt 𝕜 (fun y => f y - g y) x :=
  (hf.HasFderivAt.sub hg.HasFderivAt).DifferentiableAt
#align differentiable_at.sub DifferentiableAt.sub

theorem DifferentiableOn.sub (hf : DifferentiableOn 𝕜 f s) (hg : DifferentiableOn 𝕜 g s) :
    DifferentiableOn 𝕜 (fun y => f y - g y) s := fun x hx => (hf x hx).sub (hg x hx)
#align differentiable_on.sub DifferentiableOn.sub

@[simp]
theorem Differentiable.sub (hf : Differentiable 𝕜 f) (hg : Differentiable 𝕜 g) :
    Differentiable 𝕜 fun y => f y - g y := fun x => (hf x).sub (hg x)
#align differentiable.sub Differentiable.sub

theorem fderivWithin_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (hf : DifferentiableWithinAt 𝕜 f s x)
    (hg : DifferentiableWithinAt 𝕜 g s x) :
    fderivWithin 𝕜 (fun y => f y - g y) s x = fderivWithin 𝕜 f s x - fderivWithin 𝕜 g s x :=
  (hf.HasFderivWithinAt.sub hg.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_sub fderivWithin_sub

theorem fderiv_sub (hf : DifferentiableAt 𝕜 f x) (hg : DifferentiableAt 𝕜 g x) :
    fderiv 𝕜 (fun y => f y - g y) x = fderiv 𝕜 f x - fderiv 𝕜 g x :=
  (hf.HasFderivAt.sub hg.HasFderivAt).fderiv
#align fderiv_sub fderiv_sub

theorem HasStrictFderivAt.sub_const (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun x => f x - c) f' x := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_strict_fderiv_at.sub_const HasStrictFderivAt.sub_const

theorem HasFderivAtFilter.sub_const (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun x => f x - c) f' x L := by
  simpa only [sub_eq_add_neg] using hf.add_const (-c)
#align has_fderiv_at_filter.sub_const HasFderivAtFilter.sub_const

theorem HasFderivWithinAt.sub_const (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun x => f x - c) f' s x :=
  hf.sub_const c
#align has_fderiv_within_at.sub_const HasFderivWithinAt.sub_const

theorem HasFderivAt.sub_const (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => f x - c) f' x :=
  hf.sub_const c
#align has_fderiv_at.sub_const HasFderivAt.sub_const

theorem DifferentiableWithinAt.sub_const (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x :=
  (hf.HasFderivWithinAt.sub_const c).DifferentiableWithinAt
#align differentiable_within_at.sub_const DifferentiableWithinAt.sub_const

@[simp]
theorem differentiableWithinAt_sub_const_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => f y - c) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp only [sub_eq_add_neg, differentiableWithinAt_add_const_iff]
#align differentiable_within_at_sub_const_iff differentiableWithinAt_sub_const_iff

theorem DifferentiableAt.sub_const (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x :=
  (hf.HasFderivAt.sub_const c).DifferentiableAt
#align differentiable_at.sub_const DifferentiableAt.sub_const

@[simp]
theorem differentiableAt_sub_const_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => f y - c) x ↔ DifferentiableAt 𝕜 f x := by
  simp only [sub_eq_add_neg, differentiableAt_add_const_iff]
#align differentiable_at_sub_const_iff differentiableAt_sub_const_iff

theorem DifferentiableOn.sub_const (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s := fun x hx => (hf x hx).sub_const c
#align differentiable_on.sub_const DifferentiableOn.sub_const

@[simp]
theorem differentiableOn_sub_const_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => f y - c) s ↔ DifferentiableOn 𝕜 f s := by
  simp only [sub_eq_add_neg, differentiableOn_add_const_iff]
#align differentiable_on_sub_const_iff differentiableOn_sub_const_iff

theorem Differentiable.sub_const (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => f y - c := fun x => (hf x).sub_const c
#align differentiable.sub_const Differentiable.sub_const

@[simp]
theorem differentiable_sub_const_iff (c : F) :
    (Differentiable 𝕜 fun y => f y - c) ↔ Differentiable 𝕜 f := by
  simp only [sub_eq_add_neg, differentiable_add_const_iff]
#align differentiable_sub_const_iff differentiable_sub_const_iff

theorem fderivWithin_sub_const (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => f y - c) s x = fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_add_const hxs]
#align fderiv_within_sub_const fderivWithin_sub_const

theorem fderiv_sub_const (c : F) : fderiv 𝕜 (fun y => f y - c) x = fderiv 𝕜 f x := by
  simp only [sub_eq_add_neg, fderiv_add_const]
#align fderiv_sub_const fderiv_sub_const

theorem HasStrictFderivAt.const_sub (hf : HasStrictFderivAt f f' x) (c : F) :
    HasStrictFderivAt (fun x => c - f x) (-f') x := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_strict_fderiv_at.const_sub HasStrictFderivAt.const_sub

theorem HasFderivAtFilter.const_sub (hf : HasFderivAtFilter f f' x L) (c : F) :
    HasFderivAtFilter (fun x => c - f x) (-f') x L := by
  simpa only [sub_eq_add_neg] using hf.neg.const_add c
#align has_fderiv_at_filter.const_sub HasFderivAtFilter.const_sub

theorem HasFderivWithinAt.const_sub (hf : HasFderivWithinAt f f' s x) (c : F) :
    HasFderivWithinAt (fun x => c - f x) (-f') s x :=
  hf.const_sub c
#align has_fderiv_within_at.const_sub HasFderivWithinAt.const_sub

theorem HasFderivAt.const_sub (hf : HasFderivAt f f' x) (c : F) :
    HasFderivAt (fun x => c - f x) (-f') x :=
  hf.const_sub c
#align has_fderiv_at.const_sub HasFderivAt.const_sub

theorem DifferentiableWithinAt.const_sub (hf : DifferentiableWithinAt 𝕜 f s x) (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x :=
  (hf.HasFderivWithinAt.const_sub c).DifferentiableWithinAt
#align differentiable_within_at.const_sub DifferentiableWithinAt.const_sub

@[simp]
theorem differentiableWithinAt_const_sub_iff (c : F) :
    DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWithinAt 𝕜 f s x := by
  simp [sub_eq_add_neg]
#align differentiable_within_at_const_sub_iff differentiableWithinAt_const_sub_iff

theorem DifferentiableAt.const_sub (hf : DifferentiableAt 𝕜 f x) (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x :=
  (hf.HasFderivAt.const_sub c).DifferentiableAt
#align differentiable_at.const_sub DifferentiableAt.const_sub

@[simp]
theorem differentiableAt_const_sub_iff (c : F) :
    DifferentiableAt 𝕜 (fun y => c - f y) x ↔ DifferentiableAt 𝕜 f x := by simp [sub_eq_add_neg]
#align differentiable_at_const_sub_iff differentiableAt_const_sub_iff

theorem DifferentiableOn.const_sub (hf : DifferentiableOn 𝕜 f s) (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s := fun x hx => (hf x hx).const_sub c
#align differentiable_on.const_sub DifferentiableOn.const_sub

@[simp]
theorem differentiableOn_const_sub_iff (c : F) :
    DifferentiableOn 𝕜 (fun y => c - f y) s ↔ DifferentiableOn 𝕜 f s := by simp [sub_eq_add_neg]
#align differentiable_on_const_sub_iff differentiableOn_const_sub_iff

theorem Differentiable.const_sub (hf : Differentiable 𝕜 f) (c : F) :
    Differentiable 𝕜 fun y => c - f y := fun x => (hf x).const_sub c
#align differentiable.const_sub Differentiable.const_sub

@[simp]
theorem differentiable_const_sub_iff (c : F) :
    (Differentiable 𝕜 fun y => c - f y) ↔ Differentiable 𝕜 f := by simp [sub_eq_add_neg]
#align differentiable_const_sub_iff differentiable_const_sub_iff

theorem fderivWithin_const_sub (hxs : UniqueDiffWithinAt 𝕜 s x) (c : F) :
    fderivWithin 𝕜 (fun y => c - f y) s x = -fderivWithin 𝕜 f s x := by
  simp only [sub_eq_add_neg, fderivWithin_const_add, fderivWithin_neg, hxs]
#align fderiv_within_const_sub fderivWithin_const_sub

theorem fderiv_const_sub (c : F) : fderiv 𝕜 (fun y => c - f y) x = -fderiv 𝕜 f x := by
  simp only [← fderivWithin_univ, fderivWithin_const_sub uniqueDiffWithinAtUniv]
#align fderiv_const_sub fderiv_const_sub

end Sub

section BilinearMap

/-! ### Derivative of a bounded bilinear map -/


variable {b : E × F → G} {u : Set (E × F)}

open NormedField

theorem IsBoundedBilinearMap.hasStrictFderivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasStrictFderivAt b (h.deriv p) p :=
  by
  rw [HasStrictFderivAt]
  set T := (E × F) × E × F
  have : (fun q : T => b (q.1 - q.2)) =o[𝓝 (p, p)] fun q : T => ‖q.1 - q.2‖ * 1 :=
    by
    refine' (h.is_O'.comp_tendsto le_top).trans_is_o _
    simp only [(· ∘ ·)]
    refine'
      (is_O_refl (fun q : T => ‖q.1 - q.2‖) _).mul_is_o (is_o.norm_left <| (is_o_one_iff _).2 _)
    rw [← sub_self p]
    exact continuous_at_fst.sub continuousAt_snd
  simp only [mul_one, is_o_norm_right] at this
  refine' (is_o.congr_of_sub _).1 this
  clear this
  convert_to (fun q : T => h.deriv (p - q.2) (q.1 - q.2)) =o[𝓝 (p, p)] fun q : T => q.1 - q.2
  · ext ⟨⟨x₁, y₁⟩, ⟨x₂, y₂⟩⟩
    rcases p with ⟨x, y⟩
    simp only [isBoundedBilinearMap_deriv_coe, Prod.mk_sub_mk, h.map_sub_left, h.map_sub_right]
    abel
  have : (fun q : T => p - q.2) =o[𝓝 (p, p)] fun q => (1 : ℝ) :=
    (is_o_one_iff _).2 (sub_self p ▸ tendsto_const_nhds.sub continuousAt_snd)
  apply is_bounded_bilinear_map_apply.is_O_comp.trans_is_o
  refine' is_o.trans_is_O _ (is_O_const_mul_self 1 _ _).of_norm_right
  refine' is_o.mul_is_O _ (is_O_refl _ _)
  exact
    (((h.is_bounded_linear_map_deriv.is_O_id ⊤).comp_tendsto le_top : _).trans_is_o this).norm_left
#align is_bounded_bilinear_map.has_strict_fderiv_at IsBoundedBilinearMap.hasStrictFderivAt

theorem IsBoundedBilinearMap.hasFderivAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFderivAt b (h.deriv p) p :=
  (h.HasStrictFderivAt p).HasFderivAt
#align is_bounded_bilinear_map.has_fderiv_at IsBoundedBilinearMap.hasFderivAt

theorem IsBoundedBilinearMap.hasFderivWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    HasFderivWithinAt b (h.deriv p) u p :=
  (h.HasFderivAt p).HasFderivWithinAt
#align is_bounded_bilinear_map.has_fderiv_within_at IsBoundedBilinearMap.hasFderivWithinAt

theorem IsBoundedBilinearMap.differentiableAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableAt 𝕜 b p :=
  (h.HasFderivAt p).DifferentiableAt
#align is_bounded_bilinear_map.differentiable_at IsBoundedBilinearMap.differentiableAt

theorem IsBoundedBilinearMap.differentiableWithinAt (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    DifferentiableWithinAt 𝕜 b u p :=
  (h.DifferentiableAt p).DifferentiableWithinAt
#align is_bounded_bilinear_map.differentiable_within_at IsBoundedBilinearMap.differentiableWithinAt

theorem IsBoundedBilinearMap.fderiv (h : IsBoundedBilinearMap 𝕜 b) (p : E × F) :
    fderiv 𝕜 b p = h.deriv p :=
  HasFderivAt.fderiv (h.HasFderivAt p)
#align is_bounded_bilinear_map.fderiv IsBoundedBilinearMap.fderiv

theorem IsBoundedBilinearMap.fderivWithin (h : IsBoundedBilinearMap 𝕜 b) (p : E × F)
    (hxs : UniqueDiffWithinAt 𝕜 u p) : fderivWithin 𝕜 b u p = h.deriv p :=
  by
  rw [DifferentiableAt.fderivWithin (h.differentiable_at p) hxs]
  exact h.fderiv p
#align is_bounded_bilinear_map.fderiv_within IsBoundedBilinearMap.fderivWithin

theorem IsBoundedBilinearMap.differentiable (h : IsBoundedBilinearMap 𝕜 b) : Differentiable 𝕜 b :=
  fun x => h.DifferentiableAt x
#align is_bounded_bilinear_map.differentiable IsBoundedBilinearMap.differentiable

theorem IsBoundedBilinearMap.differentiableOn (h : IsBoundedBilinearMap 𝕜 b) :
    DifferentiableOn 𝕜 b u :=
  h.Differentiable.DifferentiableOn
#align is_bounded_bilinear_map.differentiable_on IsBoundedBilinearMap.differentiableOn

end BilinearMap

section ClmCompApply

/-! ### Derivative of the pointwise composition/application of continuous linear maps -/


variable {H : Type _} [NormedAddCommGroup H] [NormedSpace 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G} {u' : E →L[𝕜] G}

theorem HasStrictFderivAt.clm_comp (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
    HasStrictFderivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasStrictFderivAt (c x, d x)).comp x <| hc.Prod hd
#align has_strict_fderiv_at.clm_comp HasStrictFderivAt.clm_comp

theorem HasFderivWithinAt.clm_comp (hc : HasFderivWithinAt c c' s x)
    (hd : HasFderivWithinAt d d' s x) :
    HasFderivWithinAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
  (isBoundedBilinearMapComp.HasFderivAt (c x, d x)).comp_has_fderiv_within_at x <| hc.Prod hd
#align has_fderiv_within_at.clm_comp HasFderivWithinAt.clm_comp

theorem HasFderivAt.clm_comp (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
    HasFderivAt (fun y => (c y).comp (d y))
      ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
  (isBoundedBilinearMapComp.HasFderivAt (c x, d x)).comp x <| hc.Prod hd
#align has_fderiv_at.clm_comp HasFderivAt.clm_comp

theorem DifferentiableWithinAt.clm_comp (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    DifferentiableWithinAt 𝕜 (fun y => (c y).comp (d y)) s x :=
  (hc.HasFderivWithinAt.clm_comp hd.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_comp DifferentiableWithinAt.clm_comp

theorem DifferentiableAt.clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    DifferentiableAt 𝕜 (fun y => (c y).comp (d y)) x :=
  (hc.HasFderivAt.clm_comp hd.HasFderivAt).DifferentiableAt
#align differentiable_at.clm_comp DifferentiableAt.clm_comp

theorem DifferentiableOn.clm_comp (hc : DifferentiableOn 𝕜 c s) (hd : DifferentiableOn 𝕜 d s) :
    DifferentiableOn 𝕜 (fun y => (c y).comp (d y)) s := fun x hx => (hc x hx).clm_comp (hd x hx)
#align differentiable_on.clm_comp DifferentiableOn.clm_comp

theorem Differentiable.clm_comp (hc : Differentiable 𝕜 c) (hd : Differentiable 𝕜 d) :
    Differentiable 𝕜 fun y => (c y).comp (d y) := fun x => (hc x).clm_comp (hd x)
#align differentiable.clm_comp Differentiable.clm_comp

theorem fderivWithin_clm_comp (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => (c y).comp (d y)) s x =
      (compL 𝕜 F G H (c x)).comp (fderivWithin 𝕜 d s x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderivWithin 𝕜 c s x) :=
  (hc.HasFderivWithinAt.clm_comp hd.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_clm_comp fderivWithin_clm_comp

theorem fderiv_clm_comp (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => (c y).comp (d y)) x =
      (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
        ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
  (hc.HasFderivAt.clm_comp hd.HasFderivAt).fderiv
#align fderiv_clm_comp fderiv_clm_comp

theorem HasStrictFderivAt.clm_apply (hc : HasStrictFderivAt c c' x)
    (hu : HasStrictFderivAt u u' x) :
    HasStrictFderivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasStrictFderivAt (c x, u x)).comp x (hc.Prod hu)
#align has_strict_fderiv_at.clm_apply HasStrictFderivAt.clm_apply

theorem HasFderivWithinAt.clm_apply (hc : HasFderivWithinAt c c' s x)
    (hu : HasFderivWithinAt u u' s x) :
    HasFderivWithinAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
  (isBoundedBilinearMapApply.HasFderivAt (c x, u x)).comp_has_fderiv_within_at x (hc.Prod hu)
#align has_fderiv_within_at.clm_apply HasFderivWithinAt.clm_apply

theorem HasFderivAt.clm_apply (hc : HasFderivAt c c' x) (hu : HasFderivAt u u' x) :
    HasFderivAt (fun y => (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
  (isBoundedBilinearMapApply.HasFderivAt (c x, u x)).comp x (hc.Prod hu)
#align has_fderiv_at.clm_apply HasFderivAt.clm_apply

theorem DifferentiableWithinAt.clm_apply (hc : DifferentiableWithinAt 𝕜 c s x)
    (hu : DifferentiableWithinAt 𝕜 u s x) : DifferentiableWithinAt 𝕜 (fun y => (c y) (u y)) s x :=
  (hc.HasFderivWithinAt.clm_apply hu.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.clm_apply DifferentiableWithinAt.clm_apply

theorem DifferentiableAt.clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    DifferentiableAt 𝕜 (fun y => (c y) (u y)) x :=
  (hc.HasFderivAt.clm_apply hu.HasFderivAt).DifferentiableAt
#align differentiable_at.clm_apply DifferentiableAt.clm_apply

theorem DifferentiableOn.clm_apply (hc : DifferentiableOn 𝕜 c s) (hu : DifferentiableOn 𝕜 u s) :
    DifferentiableOn 𝕜 (fun y => (c y) (u y)) s := fun x hx => (hc x hx).clm_apply (hu x hx)
#align differentiable_on.clm_apply DifferentiableOn.clm_apply

theorem Differentiable.clm_apply (hc : Differentiable 𝕜 c) (hu : Differentiable 𝕜 u) :
    Differentiable 𝕜 fun y => (c y) (u y) := fun x => (hc x).clm_apply (hu x)
#align differentiable.clm_apply Differentiable.clm_apply

theorem fderivWithin_clm_apply (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (hu : DifferentiableWithinAt 𝕜 u s x) :
    fderivWithin 𝕜 (fun y => (c y) (u y)) s x =
      (c x).comp (fderivWithin 𝕜 u s x) + (fderivWithin 𝕜 c s x).flip (u x) :=
  (hc.HasFderivWithinAt.clm_apply hu.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_clm_apply fderivWithin_clm_apply

theorem fderiv_clm_apply (hc : DifferentiableAt 𝕜 c x) (hu : DifferentiableAt 𝕜 u x) :
    fderiv 𝕜 (fun y => (c y) (u y)) x = (c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x) :=
  (hc.HasFderivAt.clm_apply hu.HasFderivAt).fderiv
#align fderiv_clm_apply fderiv_clm_apply

end ClmCompApply

section Smul

/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `λ x, c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/


variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜'] [NormedSpace 𝕜' F]
  [IsScalarTower 𝕜 𝕜' F]

variable {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

theorem HasStrictFderivAt.smul (hc : HasStrictFderivAt c c' x) (hf : HasStrictFderivAt f f' x) :
    HasStrictFderivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasStrictFderivAt (c x, f x)).comp x <| hc.Prod hf
#align has_strict_fderiv_at.smul HasStrictFderivAt.smul

theorem HasFderivWithinAt.smul (hc : HasFderivWithinAt c c' s x) (hf : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) s x :=
  (isBoundedBilinearMapSmul.HasFderivAt (c x, f x)).comp_has_fderiv_within_at x <| hc.Prod hf
#align has_fderiv_within_at.smul HasFderivWithinAt.smul

theorem HasFderivAt.smul (hc : HasFderivAt c c' x) (hf : HasFderivAt f f' x) :
    HasFderivAt (fun y => c y • f y) (c x • f' + c'.smul_right (f x)) x :=
  (isBoundedBilinearMapSmul.HasFderivAt (c x, f x)).comp x <| hc.Prod hf
#align has_fderiv_at.smul HasFderivAt.smul

theorem DifferentiableWithinAt.smul (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (fun y => c y • f y) s x :=
  (hc.HasFderivWithinAt.smul hf.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.smul DifferentiableWithinAt.smul

@[simp]
theorem DifferentiableAt.smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜 (fun y => c y • f y) x :=
  (hc.HasFderivAt.smul hf.HasFderivAt).DifferentiableAt
#align differentiable_at.smul DifferentiableAt.smul

theorem DifferentiableOn.smul (hc : DifferentiableOn 𝕜 c s) (hf : DifferentiableOn 𝕜 f s) :
    DifferentiableOn 𝕜 (fun y => c y • f y) s := fun x hx => (hc x hx).smul (hf x hx)
#align differentiable_on.smul DifferentiableOn.smul

@[simp]
theorem Differentiable.smul (hc : Differentiable 𝕜 c) (hf : Differentiable 𝕜 f) :
    Differentiable 𝕜 fun y => c y • f y := fun x => (hc x).smul (hf x)
#align differentiable.smul Differentiable.smul

theorem fderivWithin_smul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hf : DifferentiableWithinAt 𝕜 f s x) :
    fderivWithin 𝕜 (fun y => c y • f y) s x =
      c x • fderivWithin 𝕜 f s x + (fderivWithin 𝕜 c s x).smul_right (f x) :=
  (hc.HasFderivWithinAt.smul hf.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_smul fderivWithin_smul

theorem fderiv_smul (hc : DifferentiableAt 𝕜 c x) (hf : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 (fun y => c y • f y) x = c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smul_right (f x) :=
  (hc.HasFderivAt.smul hf.HasFderivAt).fderiv
#align fderiv_smul fderiv_smul

theorem HasStrictFderivAt.smul_const (hc : HasStrictFderivAt c c' x) (f : F) :
    HasStrictFderivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasStrictFderivAt_const f x)
#align has_strict_fderiv_at.smul_const HasStrictFderivAt.smul_const

theorem HasFderivWithinAt.smul_const (hc : HasFderivWithinAt c c' s x) (f : F) :
    HasFderivWithinAt (fun y => c y • f) (c'.smul_right f) s x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFderivWithinAt_const f x s)
#align has_fderiv_within_at.smul_const HasFderivWithinAt.smul_const

theorem HasFderivAt.smul_const (hc : HasFderivAt c c' x) (f : F) :
    HasFderivAt (fun y => c y • f) (c'.smul_right f) x := by
  simpa only [smul_zero, zero_add] using hc.smul (hasFderivAt_const f x)
#align has_fderiv_at.smul_const HasFderivAt.smul_const

theorem DifferentiableWithinAt.smul_const (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    DifferentiableWithinAt 𝕜 (fun y => c y • f) s x :=
  (hc.HasFderivWithinAt.smul_const f).DifferentiableWithinAt
#align differentiable_within_at.smul_const DifferentiableWithinAt.smul_const

theorem DifferentiableAt.smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    DifferentiableAt 𝕜 (fun y => c y • f) x :=
  (hc.HasFderivAt.smul_const f).DifferentiableAt
#align differentiable_at.smul_const DifferentiableAt.smul_const

theorem DifferentiableOn.smul_const (hc : DifferentiableOn 𝕜 c s) (f : F) :
    DifferentiableOn 𝕜 (fun y => c y • f) s := fun x hx => (hc x hx).smul_const f
#align differentiable_on.smul_const DifferentiableOn.smul_const

theorem Differentiable.smul_const (hc : Differentiable 𝕜 c) (f : F) :
    Differentiable 𝕜 fun y => c y • f := fun x => (hc x).smul_const f
#align differentiable.smul_const Differentiable.smul_const

theorem fderivWithin_smul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (f : F) :
    fderivWithin 𝕜 (fun y => c y • f) s x = (fderivWithin 𝕜 c s x).smul_right f :=
  (hc.HasFderivWithinAt.smul_const f).fderivWithin hxs
#align fderiv_within_smul_const fderivWithin_smul_const

theorem fderiv_smul_const (hc : DifferentiableAt 𝕜 c x) (f : F) :
    fderiv 𝕜 (fun y => c y • f) x = (fderiv 𝕜 c x).smul_right f :=
  (hc.HasFderivAt.smul_const f).fderiv
#align fderiv_smul_const fderiv_smul_const

end Smul

section Mul

/-! ### Derivative of the product of two functions -/


variable {𝔸 𝔸' : Type _} [NormedRing 𝔸] [NormedCommRing 𝔸'] [NormedAlgebra 𝕜 𝔸] [NormedAlgebra 𝕜 𝔸']
  {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

theorem HasStrictFderivAt.mul' {x : E} (ha : HasStrictFderivAt a a' x)
    (hb : HasStrictFderivAt b b' x) :
    HasStrictFderivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasStrictFderivAt (a x, b x)).comp x
    (ha.Prod hb)
#align has_strict_fderiv_at.mul' HasStrictFderivAt.mul'

theorem HasStrictFderivAt.mul (hc : HasStrictFderivAt c c' x) (hd : HasStrictFderivAt d d' x) :
    HasStrictFderivAt (fun y => c y * d y) (c x • d' + d x • c') x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul HasStrictFderivAt.mul

theorem HasFderivWithinAt.mul' (ha : HasFderivWithinAt a a' s x) (hb : HasFderivWithinAt b b' s x) :
    HasFderivWithinAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt
        (a x, b x)).comp_has_fderiv_within_at
    x (ha.Prod hb)
#align has_fderiv_within_at.mul' HasFderivWithinAt.mul'

theorem HasFderivWithinAt.mul (hc : HasFderivWithinAt c c' s x) (hd : HasFderivWithinAt d d' s x) :
    HasFderivWithinAt (fun y => c y * d y) (c x • d' + d x • c') s x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul HasFderivWithinAt.mul

theorem HasFderivAt.mul' (ha : HasFderivAt a a' x) (hb : HasFderivAt b b' x) :
    HasFderivAt (fun y => a y * b y) (a x • b' + a'.smul_right (b x)) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).IsBoundedBilinearMap.HasFderivAt (a x, b x)).comp x (ha.Prod hb)
#align has_fderiv_at.mul' HasFderivAt.mul'

theorem HasFderivAt.mul (hc : HasFderivAt c c' x) (hd : HasFderivAt d d' x) :
    HasFderivAt (fun y => c y * d y) (c x • d' + d x • c') x :=
  by
  convert hc.mul' hd
  ext z
  apply mul_comm
#align has_fderiv_at.mul HasFderivAt.mul

theorem DifferentiableWithinAt.mul (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) : DifferentiableWithinAt 𝕜 (fun y => a y * b y) s x :=
  (ha.HasFderivWithinAt.mul' hb.HasFderivWithinAt).DifferentiableWithinAt
#align differentiable_within_at.mul DifferentiableWithinAt.mul

@[simp]
theorem DifferentiableAt.mul (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    DifferentiableAt 𝕜 (fun y => a y * b y) x :=
  (ha.HasFderivAt.mul' hb.HasFderivAt).DifferentiableAt
#align differentiable_at.mul DifferentiableAt.mul

theorem DifferentiableOn.mul (ha : DifferentiableOn 𝕜 a s) (hb : DifferentiableOn 𝕜 b s) :
    DifferentiableOn 𝕜 (fun y => a y * b y) s := fun x hx => (ha x hx).mul (hb x hx)
#align differentiable_on.mul DifferentiableOn.mul

@[simp]
theorem Differentiable.mul (ha : Differentiable 𝕜 a) (hb : Differentiable 𝕜 b) :
    Differentiable 𝕜 fun y => a y * b y := fun x => (ha x).mul (hb x)
#align differentiable.mul Differentiable.mul

theorem DifferentiableWithinAt.pow (ha : DifferentiableWithinAt 𝕜 a s x) :
    ∀ n : ℕ, DifferentiableWithinAt 𝕜 (fun x => a x ^ n) s x
  | 0 => by simp only [pow_zero, differentiableWithinAt_const]
  | n + 1 => by simp only [pow_succ, DifferentiableWithinAt.pow n, ha.mul]
#align differentiable_within_at.pow DifferentiableWithinAt.pow

@[simp]
theorem DifferentiableAt.pow (ha : DifferentiableAt 𝕜 a x) (n : ℕ) :
    DifferentiableAt 𝕜 (fun x => a x ^ n) x :=
  differentiableWithinAt_univ.mp <| ha.DifferentiableWithinAt.pow n
#align differentiable_at.pow DifferentiableAt.pow

theorem DifferentiableOn.pow (ha : DifferentiableOn 𝕜 a s) (n : ℕ) :
    DifferentiableOn 𝕜 (fun x => a x ^ n) s := fun x h => (ha x h).pow n
#align differentiable_on.pow DifferentiableOn.pow

@[simp]
theorem Differentiable.pow (ha : Differentiable 𝕜 a) (n : ℕ) : Differentiable 𝕜 fun x => a x ^ n :=
  fun x => (ha x).pow n
#align differentiable.pow Differentiable.pow

theorem fderivWithin_mul' (hxs : UniqueDiffWithinAt 𝕜 s x) (ha : DifferentiableWithinAt 𝕜 a s x)
    (hb : DifferentiableWithinAt 𝕜 b s x) :
    fderivWithin 𝕜 (fun y => a y * b y) s x =
      a x • fderivWithin 𝕜 b s x + (fderivWithin 𝕜 a s x).smul_right (b x) :=
  (ha.HasFderivWithinAt.mul' hb.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_mul' fderivWithin_mul'

theorem fderivWithin_mul (hxs : UniqueDiffWithinAt 𝕜 s x) (hc : DifferentiableWithinAt 𝕜 c s x)
    (hd : DifferentiableWithinAt 𝕜 d s x) :
    fderivWithin 𝕜 (fun y => c y * d y) s x =
      c x • fderivWithin 𝕜 d s x + d x • fderivWithin 𝕜 c s x :=
  (hc.HasFderivWithinAt.mul hd.HasFderivWithinAt).fderivWithin hxs
#align fderiv_within_mul fderivWithin_mul

theorem fderiv_mul' (ha : DifferentiableAt 𝕜 a x) (hb : DifferentiableAt 𝕜 b x) :
    fderiv 𝕜 (fun y => a y * b y) x = a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smul_right (b x) :=
  (ha.HasFderivAt.mul' hb.HasFderivAt).fderiv
#align fderiv_mul' fderiv_mul'

theorem fderiv_mul (hc : DifferentiableAt 𝕜 c x) (hd : DifferentiableAt 𝕜 d x) :
    fderiv 𝕜 (fun y => c y * d y) x = c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
  (hc.HasFderivAt.mul hd.HasFderivAt).fderiv
#align fderiv_mul fderiv_mul

theorem HasStrictFderivAt.mul_const' (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
    HasStrictFderivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasStrictFderivAt.comp x ha
#align has_strict_fderiv_at.mul_const' HasStrictFderivAt.mul_const'

theorem HasStrictFderivAt.mul_const (hc : HasStrictFderivAt c c' x) (d : 𝔸') :
    HasStrictFderivAt (fun y => c y * d) (d • c') x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_strict_fderiv_at.mul_const HasStrictFderivAt.mul_const

theorem HasFderivWithinAt.mul_const' (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
    HasFderivWithinAt (fun y => a y * b) (a'.smul_right b) s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFderivAt.comp_has_fderiv_within_at x ha
#align has_fderiv_within_at.mul_const' HasFderivWithinAt.mul_const'

theorem HasFderivWithinAt.mul_const (hc : HasFderivWithinAt c c' s x) (d : 𝔸') :
    HasFderivWithinAt (fun y => c y * d) (d • c') s x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_within_at.mul_const HasFderivWithinAt.mul_const

theorem HasFderivAt.mul_const' (ha : HasFderivAt a a' x) (b : 𝔸) :
    HasFderivAt (fun y => a y * b) (a'.smul_right b) x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸).flip b).HasFderivAt.comp x ha
#align has_fderiv_at.mul_const' HasFderivAt.mul_const'

theorem HasFderivAt.mul_const (hc : HasFderivAt c c' x) (d : 𝔸') :
    HasFderivAt (fun y => c y * d) (d • c') x :=
  by
  convert hc.mul_const' d
  ext z
  apply mul_comm
#align has_fderiv_at.mul_const HasFderivAt.mul_const

theorem DifferentiableWithinAt.mul_const (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => a y * b) s x :=
  (ha.HasFderivWithinAt.mul_const' b).DifferentiableWithinAt
#align differentiable_within_at.mul_const DifferentiableWithinAt.mul_const

theorem DifferentiableAt.mul_const (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => a y * b) x :=
  (ha.HasFderivAt.mul_const' b).DifferentiableAt
#align differentiable_at.mul_const DifferentiableAt.mul_const

theorem DifferentiableOn.mul_const (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => a y * b) s := fun x hx => (ha x hx).mul_const b
#align differentiable_on.mul_const DifferentiableOn.mul_const

theorem Differentiable.mul_const (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => a y * b := fun x => (ha x).mul_const b
#align differentiable.mul_const Differentiable.mul_const

theorem fderivWithin_mul_const' (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => a y * b) s x = (fderivWithin 𝕜 a s x).smul_right b :=
  (ha.HasFderivWithinAt.mul_const' b).fderivWithin hxs
#align fderiv_within_mul_const' fderivWithin_mul_const'

theorem fderivWithin_mul_const (hxs : UniqueDiffWithinAt 𝕜 s x)
    (hc : DifferentiableWithinAt 𝕜 c s x) (d : 𝔸') :
    fderivWithin 𝕜 (fun y => c y * d) s x = d • fderivWithin 𝕜 c s x :=
  (hc.HasFderivWithinAt.mul_const d).fderivWithin hxs
#align fderiv_within_mul_const fderivWithin_mul_const

theorem fderiv_mul_const' (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => a y * b) x = (fderiv 𝕜 a x).smul_right b :=
  (ha.HasFderivAt.mul_const' b).fderiv
#align fderiv_mul_const' fderiv_mul_const'

theorem fderiv_mul_const (hc : DifferentiableAt 𝕜 c x) (d : 𝔸') :
    fderiv 𝕜 (fun y => c y * d) x = d • fderiv 𝕜 c x :=
  (hc.HasFderivAt.mul_const d).fderiv
#align fderiv_mul_const fderiv_mul_const

theorem HasStrictFderivAt.const_mul (ha : HasStrictFderivAt a a' x) (b : 𝔸) :
    HasStrictFderivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasStrictFderivAt.comp x ha
#align has_strict_fderiv_at.const_mul HasStrictFderivAt.const_mul

theorem HasFderivWithinAt.const_mul (ha : HasFderivWithinAt a a' s x) (b : 𝔸) :
    HasFderivWithinAt (fun y => b * a y) (b • a') s x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFderivAt.comp_has_fderiv_within_at x ha
#align has_fderiv_within_at.const_mul HasFderivWithinAt.const_mul

theorem HasFderivAt.const_mul (ha : HasFderivAt a a' x) (b : 𝔸) :
    HasFderivAt (fun y => b * a y) (b • a') x :=
  ((ContinuousLinearMap.mul 𝕜 𝔸) b).HasFderivAt.comp x ha
#align has_fderiv_at.const_mul HasFderivAt.const_mul

theorem DifferentiableWithinAt.const_mul (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    DifferentiableWithinAt 𝕜 (fun y => b * a y) s x :=
  (ha.HasFderivWithinAt.const_mul b).DifferentiableWithinAt
#align differentiable_within_at.const_mul DifferentiableWithinAt.const_mul

theorem DifferentiableAt.const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    DifferentiableAt 𝕜 (fun y => b * a y) x :=
  (ha.HasFderivAt.const_mul b).DifferentiableAt
#align differentiable_at.const_mul DifferentiableAt.const_mul

theorem DifferentiableOn.const_mul (ha : DifferentiableOn 𝕜 a s) (b : 𝔸) :
    DifferentiableOn 𝕜 (fun y => b * a y) s := fun x hx => (ha x hx).const_mul b
#align differentiable_on.const_mul DifferentiableOn.const_mul

theorem Differentiable.const_mul (ha : Differentiable 𝕜 a) (b : 𝔸) :
    Differentiable 𝕜 fun y => b * a y := fun x => (ha x).const_mul b
#align differentiable.const_mul Differentiable.const_mul

theorem fderivWithin_const_mul (hxs : UniqueDiffWithinAt 𝕜 s x)
    (ha : DifferentiableWithinAt 𝕜 a s x) (b : 𝔸) :
    fderivWithin 𝕜 (fun y => b * a y) s x = b • fderivWithin 𝕜 a s x :=
  (ha.HasFderivWithinAt.const_mul b).fderivWithin hxs
#align fderiv_within_const_mul fderivWithin_const_mul

theorem fderiv_const_mul (ha : DifferentiableAt 𝕜 a x) (b : 𝔸) :
    fderiv 𝕜 (fun y => b * a y) x = b • fderiv 𝕜 a x :=
  (ha.HasFderivAt.const_mul b).fderiv
#align fderiv_const_mul fderiv_const_mul

end Mul

section AlgebraInverse

variable {R : Type _} [NormedRing R] [NormedAlgebra 𝕜 R] [CompleteSpace R]

open NormedRing ContinuousLinearMap Ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
theorem hasFderivAt_ring_inverse (x : Rˣ) :
    HasFderivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
  by
  have h_is_o : (fun t : R => inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] fun t : R => t :=
    by
    refine' (inverse_add_norm_diff_second_order x).trans_is_o (is_o_norm_norm.mp _)
    simp only [norm_pow, norm_norm]
    have h12 : 1 < 2 := by norm_num
    convert (Asymptotics.isO_pow_pow h12).comp_tendsto tendsto_norm_zero
    ext
    simp
  have h_lim : tendsto (fun y : R => y - x) (𝓝 x) (𝓝 0) :=
    by
    refine' tendsto_zero_iff_norm_tendsto_zero.mpr _
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id
  simp only [HasFderivAt, HasFderivAtFilter]
  convert h_is_o.comp_tendsto h_lim
  ext y
  simp only [coe_comp', Function.comp_apply, mul_left_right_apply, neg_apply, inverse_unit x,
    Units.inv_mul, add_sub_cancel'_right, mul_sub, sub_mul, one_mul, sub_neg_eq_add]
#align has_fderiv_at_ring_inverse hasFderivAt_ring_inverse

theorem differentiableAt_inverse (x : Rˣ) : DifferentiableAt 𝕜 (@Ring.inverse R _) x :=
  (hasFderivAt_ring_inverse x).DifferentiableAt
#align differentiable_at_inverse differentiableAt_inverse

theorem fderiv_inverse (x : Rˣ) : fderiv 𝕜 (@Ring.inverse R _) x = -mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
  (hasFderivAt_ring_inverse x).fderiv
#align fderiv_inverse fderiv_inverse

end AlgebraInverse

namespace ContinuousLinearEquiv

/-! ### Differentiability of linear equivs, and invariance of differentiability -/


variable (iso : E ≃L[𝕜] F)

protected theorem hasStrictFderivAt : HasStrictFderivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.HasStrictFderivAt
#align continuous_linear_equiv.has_strict_fderiv_at ContinuousLinearEquiv.hasStrictFderivAt

protected theorem hasFderivWithinAt : HasFderivWithinAt iso (iso : E →L[𝕜] F) s x :=
  iso.toContinuousLinearMap.HasFderivWithinAt
#align continuous_linear_equiv.has_fderiv_within_at ContinuousLinearEquiv.hasFderivWithinAt

protected theorem hasFderivAt : HasFderivAt iso (iso : E →L[𝕜] F) x :=
  iso.toContinuousLinearMap.HasFderivAtFilter
#align continuous_linear_equiv.has_fderiv_at ContinuousLinearEquiv.hasFderivAt

protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.HasFderivAt.DifferentiableAt
#align continuous_linear_equiv.differentiable_at ContinuousLinearEquiv.differentiableAt

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.DifferentiableAt.DifferentiableWithinAt
#align continuous_linear_equiv.differentiable_within_at ContinuousLinearEquiv.differentiableWithinAt

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.HasFderivAt.fderiv
#align continuous_linear_equiv.fderiv ContinuousLinearEquiv.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  iso.toContinuousLinearMap.fderivWithin hxs
#align continuous_linear_equiv.fderiv_within ContinuousLinearEquiv.fderivWithin

protected theorem differentiable : Differentiable 𝕜 iso := fun x => iso.DifferentiableAt
#align continuous_linear_equiv.differentiable ContinuousLinearEquiv.differentiable

protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.Differentiable.DifferentiableOn
#align continuous_linear_equiv.differentiable_on ContinuousLinearEquiv.differentiableOn

theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  by
  refine'
    ⟨fun H => _, fun H => iso.differentiable.differentiable_at.comp_differentiable_within_at x H⟩
  have : DifferentiableWithinAt 𝕜 (iso.symm ∘ iso ∘ f) s x :=
    iso.symm.differentiable.differentiable_at.comp_differentiable_within_at x H
  rwa [← Function.comp.assoc iso.symm iso f, iso.symm_comp_self] at this
#align continuous_linear_equiv.comp_differentiable_within_at_iff ContinuousLinearEquiv.comp_differentiableWithinAt_iff

theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x := by
  rw [← differentiableWithinAt_univ, ← differentiableWithinAt_univ,
    iso.comp_differentiable_within_at_iff]
#align continuous_linear_equiv.comp_differentiable_at_iff ContinuousLinearEquiv.comp_differentiableAt_iff

theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  by
  rw [DifferentiableOn, DifferentiableOn]
  simp only [iso.comp_differentiable_within_at_iff]
#align continuous_linear_equiv.comp_differentiable_on_iff ContinuousLinearEquiv.comp_differentiableOn_iff

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  by
  rw [← differentiableOn_univ, ← differentiableOn_univ]
  exact iso.comp_differentiable_on_iff
#align continuous_linear_equiv.comp_differentiable_iff ContinuousLinearEquiv.comp_differentiable_iff

theorem comp_hasFderivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFderivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFderivWithinAt f f' s x :=
  by
  refine' ⟨fun H => _, fun H => iso.has_fderiv_at.comp_has_fderiv_within_at x H⟩
  have A : f = iso.symm ∘ iso ∘ f :=
    by
    rw [← Function.comp.assoc, iso.symm_comp_self]
    rfl
  have B : f' = (iso.symm : F →L[𝕜] E).comp ((iso : E →L[𝕜] F).comp f') := by
    rw [← ContinuousLinearMap.comp_assoc, iso.coe_symm_comp_coe, ContinuousLinearMap.id_comp]
  rw [A, B]
  exact iso.symm.has_fderiv_at.comp_has_fderiv_within_at x H
#align continuous_linear_equiv.comp_has_fderiv_within_at_iff ContinuousLinearEquiv.comp_hasFderivWithinAt_iff

theorem comp_hasStrictFderivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFderivAt f f' x :=
  by
  refine' ⟨fun H => _, fun H => iso.has_strict_fderiv_at.comp x H⟩
  convert iso.symm.has_strict_fderiv_at.comp x H <;> ext z <;> apply (iso.symm_apply_apply _).symm
#align continuous_linear_equiv.comp_has_strict_fderiv_at_iff ContinuousLinearEquiv.comp_hasStrictFderivAt_iff

theorem comp_hasFderivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFderivAt f f' x := by
  simp_rw [← hasFderivWithinAt_univ, iso.comp_has_fderiv_within_at_iff]
#align continuous_linear_equiv.comp_has_fderiv_at_iff ContinuousLinearEquiv.comp_hasFderivAt_iff

theorem comp_hasFderivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFderivWithinAt (iso ∘ f) f' s x ↔ HasFderivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  by
  rw [← iso.comp_has_fderiv_within_at_iff, ← ContinuousLinearMap.comp_assoc, iso.coe_comp_coe_symm,
    ContinuousLinearMap.id_comp]
#align continuous_linear_equiv.comp_has_fderiv_within_at_iff' ContinuousLinearEquiv.comp_hasFderivWithinAt_iff'

theorem comp_hasFderivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFderivAt (iso ∘ f) f' x ↔ HasFderivAt f ((iso.symm : F →L[𝕜] E).comp f') x := by
  simp_rw [← hasFderivWithinAt_univ, iso.comp_has_fderiv_within_at_iff']
#align continuous_linear_equiv.comp_has_fderiv_at_iff' ContinuousLinearEquiv.comp_hasFderivAt_iff'

theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  by
  by_cases h : DifferentiableWithinAt 𝕜 f s x
  · rw [fderiv.comp_fderivWithin x iso.differentiable_at h hxs, iso.fderiv]
  · have : ¬DifferentiableWithinAt 𝕜 (iso ∘ f) s x := mt iso.comp_differentiable_within_at_iff.1 h
    rw [fderivWithin_zero_of_not_differentiableWithinAt h,
      fderivWithin_zero_of_not_differentiableWithinAt this, ContinuousLinearMap.comp_zero]
#align continuous_linear_equiv.comp_fderiv_within ContinuousLinearEquiv.comp_fderivWithin

theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  by
  rw [← fderivWithin_univ, ← fderivWithin_univ]
  exact iso.comp_fderiv_within uniqueDiffWithinAtUniv
#align continuous_linear_equiv.comp_fderiv ContinuousLinearEquiv.comp_fderiv

end ContinuousLinearEquiv

namespace LinearIsometryEquiv

/-! ### Differentiability of linear isometry equivs, and invariance of differentiability -/


variable (iso : E ≃ₗᵢ[𝕜] F)

protected theorem hasStrictFderivAt : HasStrictFderivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasStrictFderivAt
#align linear_isometry_equiv.has_strict_fderiv_at LinearIsometryEquiv.hasStrictFderivAt

protected theorem hasFderivWithinAt : HasFderivWithinAt iso (iso : E →L[𝕜] F) s x :=
  (iso : E ≃L[𝕜] F).HasFderivWithinAt
#align linear_isometry_equiv.has_fderiv_within_at LinearIsometryEquiv.hasFderivWithinAt

protected theorem hasFderivAt : HasFderivAt iso (iso : E →L[𝕜] F) x :=
  (iso : E ≃L[𝕜] F).HasFderivAt
#align linear_isometry_equiv.has_fderiv_at LinearIsometryEquiv.hasFderivAt

protected theorem differentiableAt : DifferentiableAt 𝕜 iso x :=
  iso.HasFderivAt.DifferentiableAt
#align linear_isometry_equiv.differentiable_at LinearIsometryEquiv.differentiableAt

protected theorem differentiableWithinAt : DifferentiableWithinAt 𝕜 iso s x :=
  iso.DifferentiableAt.DifferentiableWithinAt
#align linear_isometry_equiv.differentiable_within_at LinearIsometryEquiv.differentiableWithinAt

protected theorem fderiv : fderiv 𝕜 iso x = iso :=
  iso.HasFderivAt.fderiv
#align linear_isometry_equiv.fderiv LinearIsometryEquiv.fderiv

protected theorem fderivWithin (hxs : UniqueDiffWithinAt 𝕜 s x) : fderivWithin 𝕜 iso s x = iso :=
  (iso : E ≃L[𝕜] F).fderivWithin hxs
#align linear_isometry_equiv.fderiv_within LinearIsometryEquiv.fderivWithin

protected theorem differentiable : Differentiable 𝕜 iso := fun x => iso.DifferentiableAt
#align linear_isometry_equiv.differentiable LinearIsometryEquiv.differentiable

protected theorem differentiableOn : DifferentiableOn 𝕜 iso s :=
  iso.Differentiable.DifferentiableOn
#align linear_isometry_equiv.differentiable_on LinearIsometryEquiv.differentiableOn

theorem comp_differentiableWithinAt_iff {f : G → E} {s : Set G} {x : G} :
    DifferentiableWithinAt 𝕜 (iso ∘ f) s x ↔ DifferentiableWithinAt 𝕜 f s x :=
  (iso : E ≃L[𝕜] F).comp_differentiable_within_at_iff
#align linear_isometry_equiv.comp_differentiable_within_at_iff LinearIsometryEquiv.comp_differentiableWithinAt_iff

theorem comp_differentiableAt_iff {f : G → E} {x : G} :
    DifferentiableAt 𝕜 (iso ∘ f) x ↔ DifferentiableAt 𝕜 f x :=
  (iso : E ≃L[𝕜] F).comp_differentiable_at_iff
#align linear_isometry_equiv.comp_differentiable_at_iff LinearIsometryEquiv.comp_differentiableAt_iff

theorem comp_differentiableOn_iff {f : G → E} {s : Set G} :
    DifferentiableOn 𝕜 (iso ∘ f) s ↔ DifferentiableOn 𝕜 f s :=
  (iso : E ≃L[𝕜] F).comp_differentiable_on_iff
#align linear_isometry_equiv.comp_differentiable_on_iff LinearIsometryEquiv.comp_differentiableOn_iff

theorem comp_differentiable_iff {f : G → E} : Differentiable 𝕜 (iso ∘ f) ↔ Differentiable 𝕜 f :=
  (iso : E ≃L[𝕜] F).comp_differentiable_iff
#align linear_isometry_equiv.comp_differentiable_iff LinearIsometryEquiv.comp_differentiable_iff

theorem comp_hasFderivWithinAt_iff {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] E} :
    HasFderivWithinAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') s x ↔ HasFderivWithinAt f f' s x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff
#align linear_isometry_equiv.comp_has_fderiv_within_at_iff LinearIsometryEquiv.comp_hasFderivWithinAt_iff

theorem comp_hasStrictFderivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasStrictFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasStrictFderivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_has_strict_fderiv_at_iff
#align linear_isometry_equiv.comp_has_strict_fderiv_at_iff LinearIsometryEquiv.comp_hasStrictFderivAt_iff

theorem comp_hasFderivAt_iff {f : G → E} {x : G} {f' : G →L[𝕜] E} :
    HasFderivAt (iso ∘ f) ((iso : E →L[𝕜] F).comp f') x ↔ HasFderivAt f f' x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff
#align linear_isometry_equiv.comp_has_fderiv_at_iff LinearIsometryEquiv.comp_hasFderivAt_iff

theorem comp_hasFderivWithinAt_iff' {f : G → E} {s : Set G} {x : G} {f' : G →L[𝕜] F} :
    HasFderivWithinAt (iso ∘ f) f' s x ↔ HasFderivWithinAt f ((iso.symm : F →L[𝕜] E).comp f') s x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_within_at_iff'
#align linear_isometry_equiv.comp_has_fderiv_within_at_iff' LinearIsometryEquiv.comp_hasFderivWithinAt_iff'

theorem comp_hasFderivAt_iff' {f : G → E} {x : G} {f' : G →L[𝕜] F} :
    HasFderivAt (iso ∘ f) f' x ↔ HasFderivAt f ((iso.symm : F →L[𝕜] E).comp f') x :=
  (iso : E ≃L[𝕜] F).comp_has_fderiv_at_iff'
#align linear_isometry_equiv.comp_has_fderiv_at_iff' LinearIsometryEquiv.comp_hasFderivAt_iff'

theorem comp_fderivWithin {f : G → E} {s : Set G} {x : G} (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (iso ∘ f) s x = (iso : E →L[𝕜] F).comp (fderivWithin 𝕜 f s x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv_within hxs
#align linear_isometry_equiv.comp_fderiv_within LinearIsometryEquiv.comp_fderivWithin

theorem comp_fderiv {f : G → E} {x : G} :
    fderiv 𝕜 (iso ∘ f) x = (iso : E →L[𝕜] F).comp (fderiv 𝕜 f x) :=
  (iso : E ≃L[𝕜] F).comp_fderiv
#align linear_isometry_equiv.comp_fderiv LinearIsometryEquiv.comp_fderiv

end LinearIsometryEquiv

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a` in the strict sense, then `g` has the derivative `f'⁻¹` at `a`
in the strict sense.

This is one of the easy parts of the inverse function theorem: it assumes that we already have an
inverse function. -/
theorem HasStrictFderivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasStrictFderivAt g (f'.symm : F →L[𝕜] E) a :=
  by
  replace hg := hg.prod_map' hg
  replace hfg := hfg.prod_mk_nhds hfg
  have :
    (fun p : F × F => g p.1 - g p.2 - f'.symm (p.1 - p.2)) =O[𝓝 (a, a)] fun p : F × F =>
      f' (g p.1 - g p.2) - (p.1 - p.2) :=
    by
    refine' ((f'.symm : F →L[𝕜] E).is_O_comp _ _).congr (fun x => _) fun _ => rfl
    simp
  refine' this.trans_is_o _
  clear this
  refine'
    ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) (eventually_of_forall fun _ => rfl)).trans_is_O _
  · rintro p ⟨hp1, hp2⟩
    simp [hp1, hp2]
  · refine'
      (hf.is_O_sub_rev.comp_tendsto hg).congr' (eventually_of_forall fun _ => rfl) (hfg.mono _)
    rintro p ⟨hp1, hp2⟩
    simp only [(· ∘ ·), hp1, hp2]
#align has_strict_fderiv_at.of_local_left_inverse HasStrictFderivAt.of_local_left_inverse

/-- If `f (g y) = y` for `y` in some neighborhood of `a`, `g` is continuous at `a`, and `f` has an
invertible derivative `f'` at `g a`, then `g` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem HasFderivAt.of_local_left_inverse {f : E → F} {f' : E ≃L[𝕜] F} {g : F → E} {a : F}
    (hg : ContinuousAt g a) (hf : HasFderivAt f (f' : E →L[𝕜] F) (g a))
    (hfg : ∀ᶠ y in 𝓝 a, f (g y) = y) : HasFderivAt g (f'.symm : F →L[𝕜] E) a :=
  by
  have : (fun x : F => g x - g a - f'.symm (x - a)) =O[𝓝 a] fun x : F => f' (g x - g a) - (x - a) :=
    by
    refine' ((f'.symm : F →L[𝕜] E).is_O_comp _ _).congr (fun x => _) fun _ => rfl
    simp
  refine' this.trans_is_o _
  clear this
  refine'
    ((hf.comp_tendsto hg).symm.congr' (hfg.mono _) (eventually_of_forall fun _ => rfl)).trans_is_O _
  · rintro p hp
    simp [hp, hfg.self_of_nhds]
  · refine'
      ((hf.is_O_sub_rev f'.antilipschitz).comp_tendsto hg).congr'
        (eventually_of_forall fun _ => rfl) (hfg.mono _)
    rintro p hp
    simp only [(· ∘ ·), hp, hfg.self_of_nhds]
#align has_fderiv_at.of_local_left_inverse HasFderivAt.of_local_left_inverse

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` in the sense of strict differentiability at `f.symm a`, then `f.symm` has
the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasStrictFderivAt_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.target) (htff' : HasStrictFderivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasStrictFderivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) (f.eventually_right_inverse ha)
#align local_homeomorph.has_strict_fderiv_at_symm LocalHomeomorph.hasStrictFderivAt_symm

/-- If `f` is a local homeomorphism defined on a neighbourhood of `f.symm a`, and `f` has an
invertible derivative `f'` at `f.symm a`, then `f.symm` has the derivative `f'⁻¹` at `a`.

This is one of the easy parts of the inverse function theorem: it assumes that we already have
an inverse function. -/
theorem LocalHomeomorph.hasFderivAt_symm (f : LocalHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F}
    (ha : a ∈ f.target) (htff' : HasFderivAt f (f' : E →L[𝕜] F) (f.symm a)) :
    HasFderivAt f.symm (f'.symm : F →L[𝕜] E) a :=
  htff'.of_local_left_inverse (f.symm.ContinuousAt ha) (f.eventually_right_inverse ha)
#align local_homeomorph.has_fderiv_at_symm LocalHomeomorph.hasFderivAt_symm

theorem HasFderivWithinAt.eventually_ne (h : HasFderivWithinAt f f' s x)
    (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) : ∀ᶠ z in 𝓝[s \ {x}] x, f z ≠ f x :=
  by
  rw [nhdsWithin, diff_eq, ← inf_principal, ← inf_assoc, eventually_inf_principal]
  have A : (fun z => z - x) =O[𝓝[s] x] fun z => f' (z - x) :=
    is_O_iff.2 <| hf'.imp fun C hC => eventually_of_forall fun z => hC _
  have : (fun z => f z - f x) ~[𝓝[s] x] fun z => f' (z - x) := h.trans_is_O A
  simpa [not_imp_not, sub_eq_zero] using (A.trans this.is_O_symm).eq_zero_imp
#align has_fderiv_within_at.eventually_ne HasFderivWithinAt.eventually_ne

theorem HasFderivAt.eventually_ne (h : HasFderivAt f f' x) (hf' : ∃ C, ∀ z, ‖z‖ ≤ C * ‖f' z‖) :
    ∀ᶠ z in 𝓝[≠] x, f z ≠ f x := by
  simpa only [compl_eq_univ_diff] using (hasFderivWithinAt_univ.2 h).eventually_ne hf'
#align has_fderiv_at.eventually_ne HasFderivAt.eventually_ne

end

section

/-
  In the special case of a normed space over the reals,
  we can use  scalar multiplication in the `tendsto` characterization
  of the Fréchet derivative.
-/
variable {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F]

variable {f : E → F} {f' : E →L[ℝ] F} {x : E}

theorem has_fderiv_at_filter_real_equiv {L : Filter E} :
    Tendsto (fun x' : E => ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) ↔
      Tendsto (fun x' : E => ‖x' - x‖⁻¹ • (f x' - f x - f' (x' - x))) L (𝓝 0) :=
  by
  symm
  rw [tendsto_iff_norm_tendsto_zero]
  refine' tendsto_congr fun x' => _
  have : ‖x' - x‖⁻¹ ≥ 0 := inv_nonneg.mpr (norm_nonneg _)
  simp [norm_smul, abs_of_nonneg this]
#align has_fderiv_at_filter_real_equiv has_fderiv_at_filter_real_equiv

theorem HasFderivAt.lim_real (hf : HasFderivAt f f' x) (v : E) :
    Tendsto (fun c : ℝ => c • (f (x + c⁻¹ • v) - f x)) atTop (𝓝 (f' v)) :=
  by
  apply hf.lim v
  rw [tendsto_at_top_at_top]
  exact fun b => ⟨b, fun a ha => le_trans ha (le_abs_self _)⟩
#align has_fderiv_at.lim_real HasFderivAt.lim_real

end

section TangentCone

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜] {E : Type _} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F} {s : Set E}
  {f' : E →L[𝕜] F}

/-- The image of a tangent cone under the differential of a map is included in the tangent cone to
the image. -/
theorem HasFderivWithinAt.mapsTo_tangent_cone {x : E} (h : HasFderivWithinAt f f' s x) :
    MapsTo f' (tangentConeAt 𝕜 s x) (tangentConeAt 𝕜 (f '' s) (f x)) :=
  by
  rintro v ⟨c, d, dtop, clim, cdlim⟩
  refine'
    ⟨c, fun n => f (x + d n) - f x, mem_of_superset dtop _, clim, h.lim at_top dtop clim cdlim⟩
  simp (config := { contextual := true }) [-mem_image, mem_image_of_mem]
#align has_fderiv_within_at.maps_to_tangent_cone HasFderivWithinAt.mapsTo_tangent_cone

/-- If a set has the unique differentiability property at a point x, then the image of this set
under a map with onto derivative has also the unique differentiability property at the image point.
-/
theorem HasFderivWithinAt.uniqueDiffWithinAt {x : E} (h : HasFderivWithinAt f f' s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) (h' : DenseRange f') : UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  by
  refine' ⟨h'.dense_of_maps_to f'.continuous hs.1 _, h.continuous_within_at.mem_closure_image hs.2⟩
  show
    Submodule.span 𝕜 (tangentConeAt 𝕜 s x) ≤
      (Submodule.span 𝕜 (tangentConeAt 𝕜 (f '' s) (f x))).comap f'
  rw [Submodule.span_le]
  exact h.maps_to_tangent_cone.mono (subset.refl _) Submodule.subset_span
#align has_fderiv_within_at.unique_diff_within_at HasFderivWithinAt.uniqueDiffWithinAt

theorem UniqueDiffOn.image {f' : E → E →L[𝕜] F} (hs : UniqueDiffOn 𝕜 s)
    (hf' : ∀ x ∈ s, HasFderivWithinAt f (f' x) s x) (hd : ∀ x ∈ s, DenseRange (f' x)) :
    UniqueDiffOn 𝕜 (f '' s) :=
  ball_image_iff.2 fun x hx => (hf' x hx).UniqueDiffWithinAt (hs x hx) (hd x hx)
#align unique_diff_on.image UniqueDiffOn.image

theorem HasFderivWithinAt.uniqueDiffWithinAtOfContinuousLinearEquiv {x : E} (e' : E ≃L[𝕜] F)
    (h : HasFderivWithinAt f (e' : E →L[𝕜] F) s x) (hs : UniqueDiffWithinAt 𝕜 s x) :
    UniqueDiffWithinAt 𝕜 (f '' s) (f x) :=
  h.UniqueDiffWithinAt hs e'.Surjective.DenseRange
#align has_fderiv_within_at.unique_diff_within_at_of_continuous_linear_equiv HasFderivWithinAt.uniqueDiffWithinAtOfContinuousLinearEquiv

theorem ContinuousLinearEquiv.uniqueDiffOn_image (e : E ≃L[𝕜] F) (h : UniqueDiffOn 𝕜 s) :
    UniqueDiffOn 𝕜 (e '' s) :=
  h.image (fun x _ => e.HasFderivWithinAt) fun x hx => e.Surjective.DenseRange
#align continuous_linear_equiv.unique_diff_on_image ContinuousLinearEquiv.uniqueDiffOn_image

@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_image_iff (e : E ≃L[𝕜] F) :
    UniqueDiffOn 𝕜 (e '' s) ↔ UniqueDiffOn 𝕜 s :=
  ⟨fun h => e.symm_image_image s ▸ e.symm.unique_diff_on_image h, e.unique_diff_on_image⟩
#align continuous_linear_equiv.unique_diff_on_image_iff ContinuousLinearEquiv.uniqueDiffOn_image_iff

@[simp]
theorem ContinuousLinearEquiv.uniqueDiffOn_preimage_iff (e : F ≃L[𝕜] E) :
    UniqueDiffOn 𝕜 (e ⁻¹' s) ↔ UniqueDiffOn 𝕜 s := by
  rw [← e.image_symm_eq_preimage, e.symm.unique_diff_on_image_iff]
#align continuous_linear_equiv.unique_diff_on_preimage_iff ContinuousLinearEquiv.uniqueDiffOn_preimage_iff

end TangentCone

section RestrictScalars

/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/


variable (𝕜 : Type _) [NontriviallyNormedField 𝕜]

variable {𝕜' : Type _} [NontriviallyNormedField 𝕜'] [NormedAlgebra 𝕜 𝕜']

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace 𝕜' E]

variable [IsScalarTower 𝕜 𝕜' E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace 𝕜' F]

variable [IsScalarTower 𝕜 𝕜' F]

variable {f : E → F} {f' : E →L[𝕜'] F} {s : Set E} {x : E}

theorem HasStrictFderivAt.restrictScalars (h : HasStrictFderivAt f f' x) :
    HasStrictFderivAt f (f'.restrictScalars 𝕜) x :=
  h
#align has_strict_fderiv_at.restrict_scalars HasStrictFderivAt.restrictScalars

theorem HasFderivAtFilter.restrictScalars {L} (h : HasFderivAtFilter f f' x L) :
    HasFderivAtFilter f (f'.restrictScalars 𝕜) x L :=
  h
#align has_fderiv_at_filter.restrict_scalars HasFderivAtFilter.restrictScalars

theorem HasFderivAt.restrictScalars (h : HasFderivAt f f' x) :
    HasFderivAt f (f'.restrictScalars 𝕜) x :=
  h
#align has_fderiv_at.restrict_scalars HasFderivAt.restrictScalars

theorem HasFderivWithinAt.restrictScalars (h : HasFderivWithinAt f f' s x) :
    HasFderivWithinAt f (f'.restrictScalars 𝕜) s x :=
  h
#align has_fderiv_within_at.restrict_scalars HasFderivWithinAt.restrictScalars

theorem DifferentiableAt.restrict_scalars (h : DifferentiableAt 𝕜' f x) : DifferentiableAt 𝕜 f x :=
  (h.HasFderivAt.restrictScalars 𝕜).DifferentiableAt
#align differentiable_at.restrict_scalars DifferentiableAt.restrict_scalars

theorem DifferentiableWithinAt.restrict_scalars (h : DifferentiableWithinAt 𝕜' f s x) :
    DifferentiableWithinAt 𝕜 f s x :=
  (h.HasFderivWithinAt.restrictScalars 𝕜).DifferentiableWithinAt
#align differentiable_within_at.restrict_scalars DifferentiableWithinAt.restrict_scalars

theorem DifferentiableOn.restrict_scalars (h : DifferentiableOn 𝕜' f s) : DifferentiableOn 𝕜 f s :=
  fun x hx => (h x hx).restrictScalars 𝕜
#align differentiable_on.restrict_scalars DifferentiableOn.restrict_scalars

theorem Differentiable.restrict_scalars (h : Differentiable 𝕜' f) : Differentiable 𝕜 f := fun x =>
  (h x).restrictScalars 𝕜
#align differentiable.restrict_scalars Differentiable.restrict_scalars

theorem hasFderivWithinAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFderivWithinAt f g' s x)
    (H : f'.restrictScalars 𝕜 = g') : HasFderivWithinAt f f' s x :=
  by
  rw [← H] at h
  exact h
#align has_fderiv_within_at_of_restrict_scalars hasFderivWithinAt_of_restrictScalars

theorem hasFderivAt_of_restrictScalars {g' : E →L[𝕜] F} (h : HasFderivAt f g' x)
    (H : f'.restrictScalars 𝕜 = g') : HasFderivAt f f' x :=
  by
  rw [← H] at h
  exact h
#align has_fderiv_at_of_restrict_scalars hasFderivAt_of_restrictScalars

theorem DifferentiableAt.fderiv_restrictScalars (h : DifferentiableAt 𝕜' f x) :
    fderiv 𝕜 f x = (fderiv 𝕜' f x).restrictScalars 𝕜 :=
  (h.HasFderivAt.restrictScalars 𝕜).fderiv
#align differentiable_at.fderiv_restrict_scalars DifferentiableAt.fderiv_restrictScalars

theorem differentiableWithinAt_iff_restrictScalars (hf : DifferentiableWithinAt 𝕜 f s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    DifferentiableWithinAt 𝕜' f s x ↔
      ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderivWithin 𝕜 f s x :=
  by
  constructor
  · rintro ⟨g', hg'⟩
    exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩
  · rintro ⟨f', hf'⟩
    exact ⟨f', hasFderivWithinAt_of_restrictScalars 𝕜 hf.has_fderiv_within_at hf'⟩
#align differentiable_within_at_iff_restrict_scalars differentiableWithinAt_iff_restrictScalars

theorem differentiableAt_iff_restrictScalars (hf : DifferentiableAt 𝕜 f x) :
    DifferentiableAt 𝕜' f x ↔ ∃ g' : E →L[𝕜'] F, g'.restrictScalars 𝕜 = fderiv 𝕜 f x :=
  by
  rw [← differentiableWithinAt_univ, ← fderivWithin_univ]
  exact
    differentiableWithinAt_iff_restrictScalars 𝕜 hf.differentiable_within_at uniqueDiffWithinAtUniv
#align differentiable_at_iff_restrict_scalars differentiableAt_iff_restrictScalars

end RestrictScalars

/-! ### Support of derivatives -/


section Support

open Function

variable (𝕜 : Type _) {E F : Type _} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] {f : E → F}

theorem support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f :=
  by
  intro x
  rw [← not_imp_not]
  intro h2x
  rw [not_mem_tsupport_iff_eventuallyEq] at h2x
  exact nmem_support.mpr (h2x.fderiv_eq.trans <| fderiv_const_apply 0)
#align support_fderiv_subset support_fderiv_subset

theorem HasCompactSupport.fderiv (hf : HasCompactSupport f) : HasCompactSupport (fderiv 𝕜 f) :=
  hf.mono' <| support_fderiv_subset 𝕜
#align has_compact_support.fderiv HasCompactSupport.fderiv

end Support

