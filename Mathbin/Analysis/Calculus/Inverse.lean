/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.inverse
! leanprover-community/mathlib commit 18a5306c091183ac90884daa9373fa3b178e8607
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.ContDiff
import Mathbin.Tactic.RingExp
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.Topology.LocalHomeomorph

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_fderiv_at f f' a`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

Then we define `has_strict_fderiv_at.local_inverse` to be the `inv_fun` of this `local_homeomorph`,
and prove two versions of the inverse function theorem:

* `has_strict_fderiv_at.to_local_inverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.local_inverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `has_strict_fderiv_at.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

In the one-dimensional case we reformulate these theorems in terms of `has_strict_deriv_at` and
`f'⁻¹`.

We also reformulate the theorems in terms of `cont_diff`, to give that `C^k` (respectively,
smooth) inputs give `C^k` (smooth) inverses.  These versions require that continuous
differentiability implies strict differentiability; this is false over a general field, true over
`ℝ` or `ℂ` and implemented here assuming `is_R_or_C 𝕂`.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in `fderiv.lean`, `deriv.lean`, and `cont_diff.lean`.

## Notations

In the section about `approximates_linear_on` we introduce some `local notation` to make formulas
shorter:

* by `N` we denote `‖f'⁻¹‖`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/


open Function Set Filter Metric

open TopologicalSpace Classical Nnreal

noncomputable section

variable {𝕜 : Type _} [NontriviallyNormedField 𝕜]

variable {E : Type _} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

variable {F : Type _} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable {G : Type _} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

variable {G' : Type _} [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable {ε : ℝ}

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)

/-!
### Non-linear maps close to affine maps

In this section we study a map `f` such that `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `approximates_linear_on.to_local_homeomorph` to
be a `local_homeomorph` with `to_fun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `approximates_linear_on.to_local_homeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.
-/


/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def ApproximatesLinearOn (f : E → F) (f' : E →L[𝕜] F) (s : Set E) (c : ℝ≥0) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ‖f x - f y - f' (x - y)‖ ≤ c * ‖x - y‖
#align approximates_linear_on ApproximatesLinearOn

@[simp]
theorem approximatesLinearOnEmpty (f : E → F) (f' : E →L[𝕜] F) (c : ℝ≥0) :
    ApproximatesLinearOn f f' ∅ c := by simp [ApproximatesLinearOn]
#align approximates_linear_on_empty approximatesLinearOnEmpty

namespace ApproximatesLinearOn

variable [cs : CompleteSpace E] {f : E → F}

/-! First we prove some properties of a function that `approximates_linear_on` a (not necessarily
invertible) continuous linear map. -/


section

variable {f' : E →L[𝕜] F} {s t : Set E} {c c' : ℝ≥0}

theorem monoNum (hc : c ≤ c') (hf : ApproximatesLinearOn f f' s c) :
    ApproximatesLinearOn f f' s c' := fun x hx y hy =>
  le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc <| norm_nonneg _)
#align approximates_linear_on.mono_num ApproximatesLinearOn.monoNum

theorem monoSet (hst : s ⊆ t) (hf : ApproximatesLinearOn f f' t c) :
    ApproximatesLinearOn f f' s c := fun x hx y hy => hf x (hst hx) y (hst hy)
#align approximates_linear_on.mono_set ApproximatesLinearOn.monoSet

theorem approximates_linear_on_iff_lipschitz_on_with {f : E → F} {f' : E →L[𝕜] F} {s : Set E}
    {c : ℝ≥0} : ApproximatesLinearOn f f' s c ↔ LipschitzOnWith c (f - f') s :=
  by
  have : ∀ x y, f x - f y - f' (x - y) = (f - f') x - (f - f') y :=
    by
    intro x y
    simp only [map_sub, Pi.sub_apply]
    abel
  simp only [this, lipschitz_on_with_iff_norm_sub_le, ApproximatesLinearOn]
#align
  approximates_linear_on.approximates_linear_on_iff_lipschitz_on_with ApproximatesLinearOn.approximates_linear_on_iff_lipschitz_on_with

alias approximates_linear_on_iff_lipschitz_on_with ↔
  LipschitzOnWith _root_.lipschitz_on_with.approximates_linear_on

theorem lipschitz_sub (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith c fun x : s => f x - f' x :=
  by
  refine' LipschitzWith.of_dist_le_mul fun x y => _
  rw [dist_eq_norm, Subtype.dist_eq, dist_eq_norm]
  convert hf x x.2 y y.2 using 2
  rw [f'.map_sub]; abel
#align approximates_linear_on.lipschitz_sub ApproximatesLinearOn.lipschitz_sub

protected theorem lipschitz (hf : ApproximatesLinearOn f f' s c) :
    LipschitzWith (‖f'‖₊ + c) (s.restrict f) := by
  simpa only [restrict_apply, add_sub_cancel'_right] using
    (f'.lipschitz.restrict s).add hf.lipschitz_sub
#align approximates_linear_on.lipschitz ApproximatesLinearOn.lipschitz

protected theorem continuous (hf : ApproximatesLinearOn f f' s c) : Continuous (s.restrict f) :=
  hf.lipschitz.Continuous
#align approximates_linear_on.continuous ApproximatesLinearOn.continuous

protected theorem continuous_on (hf : ApproximatesLinearOn f f' s c) : ContinuousOn f s :=
  continuous_on_iff_continuous_restrict.2 hf.Continuous
#align approximates_linear_on.continuous_on ApproximatesLinearOn.continuous_on

end

section LocallyOnto

/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/


include cs

variable {s : Set E} {c : ℝ≥0} {f' : E →L[𝕜] F}

/-- If a function is linearly approximated by a continuous linear map with a (possibly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included in the image
of the map. -/
theorem surj_on_closed_ball_of_nonlinear_right_inverse (hf : ApproximatesLinearOn f f' s c)
    (f'symm : f'.NonlinearRightInverse) {ε : ℝ} {b : E} (ε0 : 0 ≤ ε) (hε : closedBall b ε ⊆ s) :
    SurjOn f (closedBall b ε) (closedBall (f b) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε)) :=
  by
  intro y hy
  cases' le_or_lt (f'symm.nnnorm : ℝ)⁻¹ c with hc hc
  · refine' ⟨b, by simp [ε0], _⟩
    have : dist y (f b) ≤ 0 :=
      (mem_closed_ball.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0)
    simp only [dist_le_zero] at this
    rw [this]
  have If' : (0 : ℝ) < f'symm.nnnorm := by
    rw [← inv_pos]
    exact (Nnreal.coe_nonneg _).trans_lt hc
  have Icf' : (c : ℝ) * f'symm.nnnorm < 1 := by rwa [inv_eq_one_div, lt_div_iff If'] at hc
  have Jf' : (f'symm.nnnorm : ℝ) ≠ 0 := ne_of_gt If'
  have Jcf' : (1 : ℝ) - c * f'symm.nnnorm ≠ 0 :=
    by
    apply ne_of_gt
    linarith
  /- We have to show that `y` can be written as `f x` for some `x ∈ closed_ball b ε`.
    The idea of the proof is to apply the Banach contraction principle to the map
    `g : x ↦ x + f'symm (y - f x)`, as a fixed point of this map satisfies `f x = y`.
    When `f'symm` is a genuine linear inverse, `g` is a contracting map. In our case, since `f'symm`
    is nonlinear, this map is not contracting (it is not even continuous), but still the proof of
    the contraction theorem holds: `uₙ = gⁿ b` is a Cauchy sequence, converging exponentially fast
    to the desired point `x`. Instead of appealing to general results, we check this by hand.
  
    The main point is that `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` stays in the ball on which one has a
    control. Therefore, the bound can be checked at the next step, and so on inductively.
    -/
  set g := fun x => x + f'symm (y - f x) with hg
  set u := fun n : ℕ => (g^[n]) b with hu
  have usucc : ∀ n, u (n + 1) = g (u n) := by simp [hu, ← iterate_succ_apply' g _ b]
  -- First bound: if `f z` is close to `y`, then `g z` is close to `z` (i.e., almost a fixed point).
  have A : ∀ z, dist (g z) z ≤ f'symm.nnnorm * dist (f z) y :=
    by
    intro z
    rw [dist_eq_norm, hg, add_sub_cancel', dist_eq_norm']
    exact f'symm.bound _
  -- Second bound: if `z` and `g z` are in the set with good control, then `f (g z)` becomes closer
  -- to `y` than `f z` was (this uses the linear approximation property, and is the reason for the
  -- choice of the formula for `g`).
  have B :
    ∀ z ∈ closed_ball b ε,
      g z ∈ closed_ball b ε → dist (f (g z)) y ≤ c * f'symm.nnnorm * dist (f z) y :=
    by
    intro z hz hgz
    set v := f'symm (y - f z) with hv
    calc
      dist (f (g z)) y = ‖f (z + v) - y‖ := by rw [dist_eq_norm]
      _ = ‖f (z + v) - f z - f' v + f' v - (y - f z)‖ :=
        by
        congr 1
        abel
      _ = ‖f (z + v) - f z - f' (z + v - z)‖ := by
        simp only [ContinuousLinearMap.NonlinearRightInverse.right_inv, add_sub_cancel',
          sub_add_cancel]
      _ ≤ c * ‖z + v - z‖ := hf _ (hε hgz) _ (hε hz)
      _ ≤ c * (f'symm.nnnorm * dist (f z) y) :=
        by
        apply mul_le_mul_of_nonneg_left _ (Nnreal.coe_nonneg c)
        simpa [hv, dist_eq_norm'] using f'symm.bound (y - f z)
      _ = c * f'symm.nnnorm * dist (f z) y := by ring
      
  -- Third bound: a complicated bound on `dist w b` (that will show up in the induction) is enough
  -- to check that `w` is in the ball on which one has controls. Will be used to check that `u n`
  -- belongs to this ball for all `n`.
  have C :
    ∀ (n : ℕ) (w : E),
      dist w b ≤
          f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) * dist (f b) y →
        w ∈ closed_ball b ε :=
    by
    intro n w hw
    apply hw.trans
    rw [div_mul_eq_mul_div, div_le_iff]
    swap
    · linarith
    calc
      (f'symm.nnnorm : ℝ) * (1 - (c * f'symm.nnnorm) ^ n) * dist (f b) y =
          f'symm.nnnorm * dist (f b) y * (1 - (c * f'symm.nnnorm) ^ n) :=
        by ring
      _ ≤ f'symm.nnnorm * dist (f b) y * 1 :=
        by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (Nnreal.coe_nonneg _) dist_nonneg)
        rw [sub_le_self_iff]
        exact pow_nonneg (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _)) _
      _ ≤ f'symm.nnnorm * (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε) :=
        by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_left (mem_closed_ball'.1 hy) (Nnreal.coe_nonneg _)
      _ = ε * (1 - c * f'symm.nnnorm) := by
        field_simp
        ring
      
  /- Main inductive control: `f (u n)` becomes exponentially close to `y`, and therefore
    `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
    bound on `dist (u n) b`, from which one checks that `u n` remains in the ball on which we
    have estimates. -/
  have D :
    ∀ n : ℕ,
      dist (f (u n)) y ≤ (c * f'symm.nnnorm) ^ n * dist (f b) y ∧
        dist (u n) b ≤
          f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) * dist (f b) y :=
    by
    intro n
    induction' n with n IH
    · simp [hu, le_refl]
    rw [usucc]
    have Ign :
      dist (g (u n)) b ≤
        f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n.succ) / (1 - c * f'symm.nnnorm) *
          dist (f b) y :=
      calc
        dist (g (u n)) b ≤ dist (g (u n)) (u n) + dist (u n) b := dist_triangle _ _ _
        _ ≤ f'symm.nnnorm * dist (f (u n)) y + dist (u n) b := add_le_add (A _) le_rfl
        _ ≤
            f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) +
              f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n) / (1 - c * f'symm.nnnorm) *
                dist (f b) y :=
          add_le_add (mul_le_mul_of_nonneg_left IH.1 (Nnreal.coe_nonneg _)) IH.2
        _ =
            f'symm.nnnorm * (1 - (c * f'symm.nnnorm) ^ n.succ) / (1 - c * f'symm.nnnorm) *
              dist (f b) y :=
          by
          field_simp [Jcf']
          ring
        
    refine' ⟨_, Ign⟩
    calc
      dist (f (g (u n))) y ≤ c * f'symm.nnnorm * dist (f (u n)) y :=
        B _ (C n _ IH.2) (C n.succ _ Ign)
      _ ≤ c * f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) :=
        mul_le_mul_of_nonneg_left IH.1 (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _))
      _ = (c * f'symm.nnnorm) ^ n.succ * dist (f b) y := by ring
      
  -- Deduce from the inductive bound that `uₙ` is a Cauchy sequence, therefore converging.
  have : CauchySeq u :=
    haveI :
      ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm) ^ n :=
      by
      intro n
      calc
        dist (u n) (u (n + 1)) = dist (g (u n)) (u n) := by rw [usucc, dist_comm]
        _ ≤ f'symm.nnnorm * dist (f (u n)) y := A _
        _ ≤ f'symm.nnnorm * ((c * f'symm.nnnorm) ^ n * dist (f b) y) :=
          mul_le_mul_of_nonneg_left (D n).1 (Nnreal.coe_nonneg _)
        _ = f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm) ^ n := by ring
        
    cauchy_seq_of_le_geometric _ _ Icf' this
  obtain ⟨x, hx⟩ : ∃ x, tendsto u at_top (𝓝 x) := cauchy_seq_tendsto_of_complete this
  -- As all the `uₙ` belong to the ball `closed_ball b ε`, so does their limit `x`.
  have xmem : x ∈ closed_ball b ε :=
    is_closed_ball.mem_of_tendsto hx (eventually_of_forall fun n => C n _ (D n).2)
  refine' ⟨x, xmem, _⟩
  -- It remains to check that `f x = y`. This follows from continuity of `f` on `closed_ball b ε`
  -- and from the fact that `f uₙ` is converging to `y` by construction.
  have hx' : tendsto u at_top (𝓝[closed_ball b ε] x) :=
    by
    simp only [nhdsWithin, tendsto_inf, hx, true_and_iff, ge_iff_le, tendsto_principal]
    exact eventually_of_forall fun n => C n _ (D n).2
  have T1 : tendsto (fun n => f (u n)) at_top (𝓝 (f x)) :=
    (hf.continuous_on.mono hε x xmem).Tendsto.comp hx'
  have T2 : tendsto (fun n => f (u n)) at_top (𝓝 y) :=
    by
    rw [tendsto_iff_dist_tendsto_zero]
    refine' squeeze_zero (fun n => dist_nonneg) (fun n => (D n).1) _
    simpa using
      (tendsto_pow_at_top_nhds_0_of_lt_1 (mul_nonneg (Nnreal.coe_nonneg _) (Nnreal.coe_nonneg _))
            Icf').mul
        tendsto_const_nhds
  exact tendsto_nhds_unique T1 T2
#align
  approximates_linear_on.surj_on_closed_ball_of_nonlinear_right_inverse ApproximatesLinearOn.surj_on_closed_ball_of_nonlinear_right_inverse

theorem open_image (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    (hs : IsOpen s) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : IsOpen (f '' s) :=
  by
  cases' hc with hE hc;
  · skip
    apply is_open_discrete
  simp only [is_open_iff_mem_nhds, nhds_basis_closed_ball.mem_iff, ball_image_iff] at hs⊢
  intro x hx
  rcases hs x hx with ⟨ε, ε0, hε⟩
  refine' ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, _⟩
  exact
    (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'symm (le_of_lt ε0) hε).mono hε
      (subset.refl _)
#align approximates_linear_on.open_image ApproximatesLinearOn.open_image

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (t «expr ⊆ » s) -/
theorem image_mem_nhds (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse)
    {x : E} (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : f '' s ∈ 𝓝 (f x) :=
  by
  obtain ⟨t, hts, ht, xt⟩ : ∃ (t : _)(_ : t ⊆ s), IsOpen t ∧ x ∈ t := _root_.mem_nhds_iff.1 hs
  have := IsOpen.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt)
  exact mem_of_superset this (image_subset _ hts)
#align approximates_linear_on.image_mem_nhds ApproximatesLinearOn.image_mem_nhds

theorem map_nhds_eq (hf : ApproximatesLinearOn f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E}
    (hs : s ∈ 𝓝 x) (hc : Subsingleton F ∨ c < f'symm.nnnorm⁻¹) : map f (𝓝 x) = 𝓝 (f x) :=
  by
  refine'
    le_antisymm ((hf.continuous_on x (mem_of_mem_nhds hs)).ContinuousAt hs) (le_map fun t ht => _)
  have : f '' (s ∩ t) ∈ 𝓝 (f x) :=
    (hf.mono_set (inter_subset_left s t)).image_mem_nhds f'symm (inter_mem hs ht) hc
  exact mem_of_superset this (image_subset _ (inter_subset_right _ _))
#align approximates_linear_on.map_nhds_eq ApproximatesLinearOn.map_nhds_eq

end LocallyOnto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ‖f'⁻¹‖⁻¹`. We use `N` as an abbreviation for `‖f'⁻¹‖`.
-/


variable {f' : E ≃L[𝕜] F} {s : Set E} {c : ℝ≥0}

-- mathport name: exprN
local notation "N" => ‖(f'.symm : F →L[𝕜] E)‖₊

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `antilipschitz [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `AntilipschitzWith
         [(«term_⁻¹»
           («term_-_»
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
            "-"
            `c)
           "⁻¹")
          (Term.app (Term.proj `s "." `restrict) [`f])])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `hc)]
            []
            ["with" [(Lean.binderIdent `hE) (Lean.binderIdent `hc)]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Subsingleton [`s]))]
                ":="
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`x `y]
                    []
                    "=>"
                    («term_<|_»
                     `Subtype.eq
                     "<|"
                     (Term.app
                      (Term.explicit "@" `Subsingleton.elim)
                      [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))]
                 "⟩"))))
             []
             (Tactic.exact "exact" `AntilipschitzWith.of_subsingleton)])
           []
           (convert
            "convert"
            []
            (Term.app
             (Term.proj (Term.app `f'.antilipschitz.restrict [`s]) "." `add_lipschitz_with)
             [`hf.lipschitz_sub `hc])
            [])
           []
           (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `restrict)] "]"] [])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `hc)]
           []
           ["with" [(Lean.binderIdent `hE) (Lean.binderIdent `hc)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `Subsingleton [`s]))]
               ":="
               (Term.anonymousCtor
                "⟨"
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`x `y]
                   []
                   "=>"
                   («term_<|_»
                    `Subtype.eq
                    "<|"
                    (Term.app
                     (Term.explicit "@" `Subsingleton.elim)
                     [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))]
                "⟩"))))
            []
            (Tactic.exact "exact" `AntilipschitzWith.of_subsingleton)])
          []
          (convert
           "convert"
           []
           (Term.app
            (Term.proj (Term.app `f'.antilipschitz.restrict [`s]) "." `add_lipschitz_with)
            [`hf.lipschitz_sub `hc])
           [])
          []
          (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `restrict)] "]"] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] ["[" [(Tactic.simpLemma [] [] `restrict)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `restrict
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (convert
       "convert"
       []
       (Term.app
        (Term.proj (Term.app `f'.antilipschitz.restrict [`s]) "." `add_lipschitz_with)
        [`hf.lipschitz_sub `hc])
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `f'.antilipschitz.restrict [`s]) "." `add_lipschitz_with)
       [`hf.lipschitz_sub `hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf.lipschitz_sub
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `f'.antilipschitz.restrict [`s]) "." `add_lipschitz_with)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f'.antilipschitz.restrict [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f'.antilipschitz.restrict
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `f'.antilipschitz.restrict [`s])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.tacticHaveI_
         "haveI"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `Subsingleton [`s]))]
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`x `y]
               []
               "=>"
               («term_<|_»
                `Subtype.eq
                "<|"
                (Term.app
                 (Term.explicit "@" `Subsingleton.elim)
                 [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))]
            "⟩"))))
        []
        (Tactic.exact "exact" `AntilipschitzWith.of_subsingleton)])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `AntilipschitzWith.of_subsingleton)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `AntilipschitzWith.of_subsingleton
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticHaveI_
       "haveI"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec ":" (Term.app `Subsingleton [`s]))]
         ":="
         (Term.anonymousCtor
          "⟨"
          [(Term.fun
            "fun"
            (Term.basicFun
             [`x `y]
             []
             "=>"
             («term_<|_»
              `Subtype.eq
              "<|"
              (Term.app
               (Term.explicit "@" `Subsingleton.elim)
               [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))]
          "⟩"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`x `y]
          []
          "=>"
          («term_<|_»
           `Subtype.eq
           "<|"
           (Term.app
            (Term.explicit "@" `Subsingleton.elim)
            [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `y]
        []
        "=>"
        («term_<|_»
         `Subtype.eq
         "<|"
         (Term.app
          (Term.explicit "@" `Subsingleton.elim)
          [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `Subtype.eq
       "<|"
       (Term.app
        (Term.explicit "@" `Subsingleton.elim)
        [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.explicit "@" `Subsingleton.elim)
       [(Term.hole "_") `hE (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hE
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.explicit "@" `Subsingleton.elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subsingleton.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `Subtype.eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subsingleton [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subsingleton
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases'
       "cases'"
       [(Tactic.casesTarget [] `hc)]
       []
       ["with" [(Lean.binderIdent `hE) (Lean.binderIdent `hc)]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `AntilipschitzWith
       [(«term_⁻¹»
         («term_-_»
          («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
          "-"
          `c)
         "⁻¹")
        (Term.app (Term.proj `s "." `restrict) [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s "." `restrict) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `s "." `restrict)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `s "." `restrict) [`f])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_⁻¹»
       («term_-_»
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
        "-"
        `c)
       "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹") "-" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    antilipschitz
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : AntilipschitzWith N ⁻¹ - c ⁻¹ s . restrict f
    :=
      by
        cases' hc with hE hc
          ·
            haveI : Subsingleton s := ⟨ fun x y => Subtype.eq <| @ Subsingleton.elim _ hE _ _ ⟩
              exact AntilipschitzWith.of_subsingleton
          convert f'.antilipschitz.restrict s . add_lipschitz_with hf.lipschitz_sub hc
          simp [ restrict ]
#align approximates_linear_on.antilipschitz ApproximatesLinearOn.antilipschitz

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `injective [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `Injective [(Term.app (Term.proj `s "." `restrict) [`f])])))
      (Command.declValSimple
       ":="
       (Term.proj (Term.app (Term.proj `hf "." `antilipschitz) [`hc]) "." `Injective)
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `hf "." `antilipschitz) [`hc]) "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `antilipschitz) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `antilipschitz)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `antilipschitz) [`hc])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `Injective [(Term.app (Term.proj `s "." `restrict) [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `s "." `restrict) [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `s "." `restrict)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `s "." `restrict) [`f])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Injective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    injective
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : Injective s . restrict f
    := hf . antilipschitz hc . Injective
#align approximates_linear_on.injective ApproximatesLinearOn.injective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `inj_on [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `InjOn [`f `s])))
      (Command.declValSimple
       ":="
       («term_<|_»
        (Term.proj `injOn_iff_injective "." (fieldIdx "2"))
        "<|"
        (Term.app (Term.proj `hf "." `Injective) [`hc]))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `injOn_iff_injective "." (fieldIdx "2"))
       "<|"
       (Term.app (Term.proj `hf "." `Injective) [`hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `Injective) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `Injective)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `injOn_iff_injective "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `injOn_iff_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `InjOn [`f `s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `InjOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    inj_on
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : InjOn f s
    := injOn_iff_injective . 2 <| hf . Injective hc
#align approximates_linear_on.inj_on ApproximatesLinearOn.inj_on

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `surjective [])
      (Command.declSig
       [(Term.instBinder "[" [] (Term.app `CompleteSpace [`E]) "]")
        (Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `univ
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec ":" (Term.app `Surjective [`f])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.cases'
            "cases'"
            [(Tactic.casesTarget [] `hc)]
            []
            ["with" [(Lean.binderIdent `hE) (Lean.binderIdent `hc)]])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.tacticHaveI_
              "haveI"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" (Term.app `Subsingleton [`F]))]
                ":="
                (Term.app
                 (Term.proj
                  (Term.app `Equiv.subsingleton_congr [`f'.to_linear_equiv.to_equiv])
                  "."
                  (fieldIdx "1"))
                 [`hE]))))
             []
             (Tactic.exact "exact" (Term.app `surjective_to_subsingleton [(Term.hole "_")]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.apply
              "apply"
              (Term.app
               `forall_of_forall_mem_closed_ball
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`y]
                  [(Term.typeSpec ":" `F)]
                  "=>"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                   ","
                   («term_=_» (Term.app `f [`a]) "=" `y))))
                (Term.app `f [(num "0")])
                (Term.hole "_")]))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hc' []]
                [(Term.typeSpec
                  ":"
                  («term_<_»
                   (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                   "<"
                   («term_-_»
                    («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                    "-"
                    `c)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_pos)] "]")
                     [])
                    []
                    (Tactic.exact "exact" `hc)]))))))
             []
             (Tactic.tacticLet_
              "let"
              (Term.letDecl
               (Term.letIdDecl
                `p
                []
                [(Term.typeSpec
                  ":"
                  (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" (Term.prop "Prop")))]
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`R]
                  []
                  "=>"
                  («term_⊆_»
                   (Term.app `closed_ball [(Term.app `f [(num "0")]) `R])
                   "⊆"
                   (Term.app `Set.range [`f])))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hp []]
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `r)
                     [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                   " in "
                   `at_top
                   ", "
                   (Term.app
                    `p
                    [(«term_*_»
                      («term_-_»
                       («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                       "-"
                       `c)
                      "*"
                      `r)])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`hr []]
                       [(Term.typeSpec
                         ":"
                         (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                          "∀ᶠ"
                          (Std.ExtendedBinder.extBinders
                           (Std.ExtendedBinder.extBinder
                            (Lean.binderIdent `r)
                            [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                          " in "
                          `at_top
                          ", "
                          («term_≤_» (num "0") "≤" `r)))]
                       ":="
                       (Term.app `eventually_ge_at_top [(num "0")]))))
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `hr.mono
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`r `hr]
                         []
                         "=>"
                         (Term.app
                          `subset.trans
                          [(Term.hole "_")
                           (Term.app
                            `image_subset_range
                            [`f (Term.app `closed_ball [(num "0") `r])])])))]))
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      `hf.surj_on_closed_ball_of_nonlinear_right_inverse
                      [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
                    []
                    (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))]))))))
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
                 [`hp.frequently])
                "."
                `mono)
               [(Term.hole "_")]))
             []
             (Tactic.exact
              "exact"
              (Term.fun "fun" (Term.basicFun [`R `h `y `hy] [] "=>" (Term.app `h [`hy]))))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.cases'
           "cases'"
           [(Tactic.casesTarget [] `hc)]
           []
           ["with" [(Lean.binderIdent `hE) (Lean.binderIdent `hc)]])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.tacticHaveI_
             "haveI"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" (Term.app `Subsingleton [`F]))]
               ":="
               (Term.app
                (Term.proj
                 (Term.app `Equiv.subsingleton_congr [`f'.to_linear_equiv.to_equiv])
                 "."
                 (fieldIdx "1"))
                [`hE]))))
            []
            (Tactic.exact "exact" (Term.app `surjective_to_subsingleton [(Term.hole "_")]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.apply
             "apply"
             (Term.app
              `forall_of_forall_mem_closed_ball
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`y]
                 [(Term.typeSpec ":" `F)]
                 "=>"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                  ","
                  («term_=_» (Term.app `f [`a]) "=" `y))))
               (Term.app `f [(num "0")])
               (Term.hole "_")]))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hc' []]
               [(Term.typeSpec
                 ":"
                 («term_<_»
                  (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
                  "<"
                  («term_-_»
                   («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                   "-"
                   `c)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_pos)] "]")
                    [])
                   []
                   (Tactic.exact "exact" `hc)]))))))
            []
            (Tactic.tacticLet_
             "let"
             (Term.letDecl
              (Term.letIdDecl
               `p
               []
               [(Term.typeSpec ":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" (Term.prop "Prop")))]
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`R]
                 []
                 "=>"
                 («term_⊆_»
                  (Term.app `closed_ball [(Term.app `f [(num "0")]) `R])
                  "⊆"
                  (Term.app `Set.range [`f])))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`hp []]
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Std.ExtendedBinder.extBinders
                   (Std.ExtendedBinder.extBinder
                    (Lean.binderIdent `r)
                    [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                  " in "
                  `at_top
                  ", "
                  (Term.app
                   `p
                   [(«term_*_»
                     («term_-_»
                      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                      "-"
                      `c)
                     "*"
                     `r)])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`hr []]
                      [(Term.typeSpec
                        ":"
                        (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                         "∀ᶠ"
                         (Std.ExtendedBinder.extBinders
                          (Std.ExtendedBinder.extBinder
                           (Lean.binderIdent `r)
                           [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                         " in "
                         `at_top
                         ", "
                         («term_≤_» (num "0") "≤" `r)))]
                      ":="
                      (Term.app `eventually_ge_at_top [(num "0")]))))
                   []
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `hr.mono
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`r `hr]
                        []
                        "=>"
                        (Term.app
                         `subset.trans
                         [(Term.hole "_")
                          (Term.app
                           `image_subset_range
                           [`f (Term.app `closed_ball [(num "0") `r])])])))]))
                   []
                   (Tactic.refine'
                    "refine'"
                    (Term.app
                     `hf.surj_on_closed_ball_of_nonlinear_right_inverse
                     [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
                   []
                   (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))]))))))
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
                [`hp.frequently])
               "."
               `mono)
              [(Term.hole "_")]))
            []
            (Tactic.exact
             "exact"
             (Term.fun "fun" (Term.basicFun [`R `h `y `hy] [] "=>" (Term.app `h [`hy]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.apply
         "apply"
         (Term.app
          `forall_of_forall_mem_closed_ball
          [(Term.fun
            "fun"
            (Term.basicFun
             [`y]
             [(Term.typeSpec ":" `F)]
             "=>"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
              ","
              («term_=_» (Term.app `f [`a]) "=" `y))))
           (Term.app `f [(num "0")])
           (Term.hole "_")]))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hc' []]
           [(Term.typeSpec
             ":"
             («term_<_»
              (Term.typeAscription "(" (num "0") ":" [(Data.Real.Basic.termℝ "ℝ")] ")")
              "<"
              («term_-_»
               («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
               "-"
               `c)))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_pos)] "]") [])
               []
               (Tactic.exact "exact" `hc)]))))))
        []
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `p
           []
           [(Term.typeSpec ":" (Term.arrow (Data.Real.Basic.termℝ "ℝ") "→" (Term.prop "Prop")))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`R]
             []
             "=>"
             («term_⊆_»
              (Term.app `closed_ball [(Term.app `f [(num "0")]) `R])
              "⊆"
              (Term.app `Set.range [`f])))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hp []]
           [(Term.typeSpec
             ":"
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Std.ExtendedBinder.extBinders
               (Std.ExtendedBinder.extBinder
                (Lean.binderIdent `r)
                [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
              " in "
              `at_top
              ", "
              (Term.app
               `p
               [(«term_*_»
                 («term_-_»
                  («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                  "-"
                  `c)
                 "*"
                 `r)])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hr []]
                  [(Term.typeSpec
                    ":"
                    (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                     "∀ᶠ"
                     (Std.ExtendedBinder.extBinders
                      (Std.ExtendedBinder.extBinder
                       (Lean.binderIdent `r)
                       [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                     " in "
                     `at_top
                     ", "
                     («term_≤_» (num "0") "≤" `r)))]
                  ":="
                  (Term.app `eventually_ge_at_top [(num "0")]))))
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 `hr.mono
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`r `hr]
                    []
                    "=>"
                    (Term.app
                     `subset.trans
                     [(Term.hole "_")
                      (Term.app
                       `image_subset_range
                       [`f (Term.app `closed_ball [(num "0") `r])])])))]))
               []
               (Tactic.refine'
                "refine'"
                (Term.app
                 `hf.surj_on_closed_ball_of_nonlinear_right_inverse
                 [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
               []
               (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))]))))))
        []
        (Tactic.refine'
         "refine'"
         (Term.app
          (Term.proj
           (Term.app
            (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
            [`hp.frequently])
           "."
           `mono)
          [(Term.hole "_")]))
        []
        (Tactic.exact
         "exact"
         (Term.fun "fun" (Term.basicFun [`R `h `y `hy] [] "=>" (Term.app `h [`hy]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun "fun" (Term.basicFun [`R `h `y `hy] [] "=>" (Term.app `h [`hy]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`R `h `y `hy] [] "=>" (Term.app `h [`hy])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`hy])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `R
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
          [`hp.frequently])
         "."
         `mono)
        [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
         [`hp.frequently])
        "."
        `mono)
       [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
        [`hp.frequently])
       "."
       `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
       [`hp.frequently])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hp.frequently
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `tendsto_id.const_mul_at_top [`hc']) "." `Frequently)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `tendsto_id.const_mul_at_top [`hc'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `tendsto_id.const_mul_at_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `tendsto_id.const_mul_at_top [`hc'])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj
       (Term.paren "(" (Term.app `tendsto_id.const_mul_at_top [`hc']) ")")
       "."
       `Frequently)
      [`hp.frequently])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hp []]
         [(Term.typeSpec
           ":"
           (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
            "∀ᶠ"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `r)
              [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
            " in "
            `at_top
            ", "
            (Term.app
             `p
             [(«term_*_»
               («term_-_»
                («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                "-"
                `c)
               "*"
               `r)])))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`hr []]
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Std.ExtendedBinder.extBinders
                    (Std.ExtendedBinder.extBinder
                     (Lean.binderIdent `r)
                     [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                   " in "
                   `at_top
                   ", "
                   («term_≤_» (num "0") "≤" `r)))]
                ":="
                (Term.app `eventually_ge_at_top [(num "0")]))))
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `hr.mono
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`r `hr]
                  []
                  "=>"
                  (Term.app
                   `subset.trans
                   [(Term.hole "_")
                    (Term.app
                     `image_subset_range
                     [`f (Term.app `closed_ball [(num "0") `r])])])))]))
             []
             (Tactic.refine'
              "refine'"
              (Term.app
               `hf.surj_on_closed_ball_of_nonlinear_right_inverse
               [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
             []
             (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hr []]
             [(Term.typeSpec
               ":"
               (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                "∀ᶠ"
                (Std.ExtendedBinder.extBinders
                 (Std.ExtendedBinder.extBinder
                  (Lean.binderIdent `r)
                  [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
                " in "
                `at_top
                ", "
                («term_≤_» (num "0") "≤" `r)))]
             ":="
             (Term.app `eventually_ge_at_top [(num "0")]))))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `hr.mono
            [(Term.fun
              "fun"
              (Term.basicFun
               [`r `hr]
               []
               "=>"
               (Term.app
                `subset.trans
                [(Term.hole "_")
                 (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])])))]))
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            `hf.surj_on_closed_ball_of_nonlinear_right_inverse
            [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
          []
          (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `subset_univ [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `subset_univ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset_univ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `hf.surj_on_closed_ball_of_nonlinear_right_inverse
        [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hf.surj_on_closed_ball_of_nonlinear_right_inverse
       [`f'.to_nonlinear_right_inverse `hr (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'.to_nonlinear_right_inverse
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.surj_on_closed_ball_of_nonlinear_right_inverse
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        `hr.mono
        [(Term.fun
          "fun"
          (Term.basicFun
           [`r `hr]
           []
           "=>"
           (Term.app
            `subset.trans
            [(Term.hole "_")
             (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `hr.mono
       [(Term.fun
         "fun"
         (Term.basicFun
          [`r `hr]
          []
          "=>"
          (Term.app
           `subset.trans
           [(Term.hole "_")
            (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`r `hr]
        []
        "=>"
        (Term.app
         `subset.trans
         [(Term.hole "_")
          (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `subset.trans
       [(Term.hole "_") (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `image_subset_range [`f (Term.app `closed_ball [(num "0") `r])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `closed_ball [(num "0") `r])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closed_ball
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `closed_ball [(num "0") `r])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `image_subset_range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `image_subset_range [`f (Term.paren "(" (Term.app `closed_ball [(num "0") `r]) ")")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `subset.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `r
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hr.mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hr []]
         [(Term.typeSpec
           ":"
           (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
            "∀ᶠ"
            (Std.ExtendedBinder.extBinders
             (Std.ExtendedBinder.extBinder
              (Lean.binderIdent `r)
              [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
            " in "
            `at_top
            ", "
            («term_≤_» (num "0") "≤" `r)))]
         ":="
         (Term.app `eventually_ge_at_top [(num "0")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eventually_ge_at_top [(num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eventually_ge_at_top
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
       "∀ᶠ"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `r)
         [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
       " in "
       `at_top
       ", "
       («term_≤_» (num "0") "≤" `r))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_≤_» (num "0") "≤" `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `at_top
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
       "∀ᶠ"
       (Std.ExtendedBinder.extBinders
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `r)
         [(group ":" (Data.Real.Basic.termℝ "ℝ"))]))
       " in "
       `at_top
       ", "
       (Term.app
        `p
        [(«term_*_»
          («term_-_»
           («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
           "-"
           `c)
          "*"
          `r)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `p
       [(«term_*_»
         («term_-_»
          («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
          "-"
          `c)
         "*"
         `r)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_-_»
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
        "-"
        `c)
       "*"
       `r)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `r
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹") "-" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    surjective
    [ CompleteSpace E ]
        ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) univ c )
        ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : Surjective f
    :=
      by
        cases' hc with hE hc
          ·
            haveI : Subsingleton F := Equiv.subsingleton_congr f'.to_linear_equiv.to_equiv . 1 hE
              exact surjective_to_subsingleton _
          ·
            apply forall_of_forall_mem_closed_ball fun y : F => ∃ a , f a = y f 0 _
              have hc' : ( 0 : ℝ ) < N ⁻¹ - c := by rw [ sub_pos ] exact hc
              let p : ℝ → Prop := fun R => closed_ball f 0 R ⊆ Set.range f
              have
                hp
                  : ∀ᶠ r : ℝ in at_top , p N ⁻¹ - c * r
                  :=
                  by
                    have hr : ∀ᶠ r : ℝ in at_top , 0 ≤ r := eventually_ge_at_top 0
                      refine'
                        hr.mono fun r hr => subset.trans _ image_subset_range f closed_ball 0 r
                      refine'
                        hf.surj_on_closed_ball_of_nonlinear_right_inverse
                          f'.to_nonlinear_right_inverse hr _
                      exact subset_univ _
              refine' tendsto_id.const_mul_at_top hc' . Frequently hp.frequently . mono _
              exact fun R h y hy => h hy
#align approximates_linear_on.surjective ApproximatesLinearOn.surjective

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A map approximating a linear equivalence on a set defines a local equivalence on this set.\nShould not be used outside of this file, because it is superseded by `to_local_homeomorph` below.\n\nThis is a first step towards the inverse function. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toLocalEquiv [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       [(Term.typeSpec ":" (Term.app `LocalEquiv [`E `F]))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj (Term.app (Term.proj `hf "." `InjOn) [`hc]) "." `toLocalEquiv)
        [(Term.hole "_") (Term.hole "_")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app (Term.proj `hf "." `InjOn) [`hc]) "." `toLocalEquiv)
       [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app (Term.proj `hf "." `InjOn) [`hc]) "." `toLocalEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `InjOn) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `InjOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `InjOn) [`hc])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LocalEquiv [`E `F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LocalEquiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    A map approximating a linear equivalence on a set defines a local equivalence on this set.
    Should not be used outside of this file, because it is superseded by `to_local_homeomorph` below.
    
    This is a first step towards the inverse function. -/
  def
    toLocalEquiv
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : LocalEquiv E F
    := hf . InjOn hc . toLocalEquiv _ _
#align approximates_linear_on.to_local_equiv ApproximatesLinearOn.toLocalEquiv

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `inverse_continuous_on [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ContinuousOn
         [(Term.proj (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc]) "." `symm)
          (Set.Data.Set.Image.term_''_ `f " '' " `s)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.apply
            "apply"
            (Term.proj `continuous_on_iff_continuous_restrict "." (fieldIdx "2")))
           []
           (Tactic.refine'
            "refine'"
            (Term.proj
             (Term.app
              (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
              [(Term.hole "_") (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')])
             "."
             `Continuous))
           []
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [`x `hx]
              []
              "=>"
              (Term.app
               (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target)
               [`hx]))))])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply
           "apply"
           (Term.proj `continuous_on_iff_continuous_restrict "." (fieldIdx "2")))
          []
          (Tactic.refine'
           "refine'"
           (Term.proj
            (Term.app
             (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
             [(Term.hole "_") (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')])
            "."
            `Continuous))
          []
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [`x `hx]
             []
             "=>"
             (Term.app (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target) [`hx]))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.fun
        "fun"
        (Term.basicFun
         [`x `hx]
         []
         "=>"
         (Term.app (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target) [`hx]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x `hx]
        []
        "=>"
        (Term.app (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target) [`hx])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target) [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `map_target)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.to_local_equiv [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.to_local_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.to_local_equiv [`hc]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.proj
        (Term.app
         (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
         [(Term.hole "_") (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')])
        "."
        `Continuous))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj
       (Term.app
        (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
        [(Term.hole "_") (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')])
       "."
       `Continuous)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
       [(Term.hole "_") (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hf.to_local_equiv [`hc]) "." `right_inv')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.to_local_equiv [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.to_local_equiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.to_local_equiv [`hc]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `to_right_inv_on')
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.antilipschitz [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.antilipschitz
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hf.antilipschitz [`hc]) ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj (Term.paren "(" (Term.app `hf.antilipschitz [`hc]) ")") "." `to_right_inv_on')
      [(Term.hole "_")
       (Term.proj (Term.paren "(" (Term.app `hf.to_local_equiv [`hc]) ")") "." `right_inv')])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" (Term.proj `continuous_on_iff_continuous_restrict "." (fieldIdx "2")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `continuous_on_iff_continuous_restrict "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `continuous_on_iff_continuous_restrict
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `ContinuousOn
       [(Term.proj (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc]) "." `symm)
        (Set.Data.Set.Image.term_''_ `f " '' " `s)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_ `f " '' " `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_ `f " '' " `s)
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc]) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `ContinuousOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
  theorem
    inverse_continuous_on
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : ContinuousOn hf . toLocalEquiv hc . symm f '' s
    :=
      by
        apply continuous_on_iff_continuous_restrict . 2
          refine'
            hf.antilipschitz hc . to_right_inv_on' _ hf.to_local_equiv hc . right_inv' . Continuous
          exact fun x hx => hf.to_local_equiv hc . map_target hx
#align approximates_linear_on.inverse_continuous_on ApproximatesLinearOn.inverse_continuous_on

/- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[["[", expr mul_le_mul_of_nonneg_left, ",", expr nnreal.coe_nonneg, "]"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The inverse function is approximated linearly on `f '' s` by `f'.symm`. -/")]
      []
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `toInv [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `ApproximatesLinearOn
         [(Term.proj (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc]) "." `symm)
          (Term.typeAscription
           "("
           (Term.proj `f' "." `symm)
           ":"
           [(Topology.Algebra.Module.Basic.«term_→L[_]_» `F " →L[" `𝕜 "] " `E)]
           ")")
          (Set.Data.Set.Image.term_''_ `f " '' " `s)
          («term_*_»
           («term_*_»
            (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
            "*"
            («term_⁻¹»
             («term_-_»
              («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
              "-"
              `c)
             "⁻¹"))
           "*"
           `c)])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.intro "intro" [`x `hx `y `hy])
           []
           (Mathlib.Tactic.set
            "set"
            []
            (Mathlib.Tactic.setArgsRest
             `A
             []
             ":="
             (Term.app `hf.to_local_equiv [`hc])
             ["with" [] `hA]))
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`Af []]
              [(Term.typeSpec
                ":"
                (Term.forall
                 "∀"
                 [`z]
                 []
                 ","
                 («term_=_» (Term.app `A [`z]) "=" (Term.app `f [`z]))))]
              ":="
              (Term.fun "fun" (Term.basicFun [`z] [] "=>" `rfl)))))
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               (Term.proj
                (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                (fieldIdx "1"))
               [`hx]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x's)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])
              [])])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget
              []
              (Term.app
               (Term.proj
                (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "."
                (fieldIdx "1"))
               [`hy]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y's)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                   [])]
                 "⟩")])
              [])])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Af [`x']))
              ","
              (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Af [`y']))
              ","
              (Tactic.rwRule [] (Term.app `A.left_inv [`x's]))
              ","
              (Tactic.rwRule [] (Term.app `A.left_inv [`y's]))]
             "]")
            [])
           []
           (calcTactic
            "calc"
            (calcStep
             («term_≤_»
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               («term_-_»
                («term_-_» `x' "-" `y')
                "-"
                (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))
               "‖")
              "≤"
              («term_*_»
               (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                (Term.app
                 `f'
                 [(«term_-_»
                   («term_-_» `x' "-" `y')
                   "-"
                   (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))])
                "‖")))
             ":="
             (Term.app
              (Term.proj
               (Term.typeAscription
                "("
                `f'
                ":"
                [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
                ")")
               "."
               `bound_of_antilipschitz)
              [`f'.antilipschitz (Term.hole "_")]))
            [(calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_-_»
                  («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
                  "-"
                  (Term.app `f' [(«term_-_» `y' "-" `x')]))
                 "‖")))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.congr "congr" [(num "2")])
                  []
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `ContinuousLinearEquiv.apply_symm_apply)
                     ","
                     (Tactic.simpLemma [] [] `ContinuousLinearEquiv.map_sub)]
                    "]"]
                   [])
                  []
                  (Tactic.abel "abel" [] [])]))))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
                "*"
                («term_*_»
                 `c
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y' "-" `x') "‖"))))
              ":="
              (Term.app
               `mul_le_mul_of_nonneg_left
               [(Term.app `hf [(Term.hole "_") `y's (Term.hole "_") `x's])
                (Term.app `Nnreal.coe_nonneg [(Term.hole "_")])]))
             (calcStep
              («term_≤_»
               (Term.hole "_")
               "≤"
               («term_*_»
                (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
                "*"
                («term_*_»
                 `c
                 "*"
                 («term_*_»
                  (Term.typeAscription
                   "("
                   («term_⁻¹»
                    («term_-_»
                     («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                     "-"
                     `c)
                    "⁻¹")
                   ":"
                   [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
                   ")")
                  "*"
                  (Analysis.Normed.Group.Basic.«term‖_‖»
                   "‖"
                   («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
                   "‖")))))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(choice
                   (Tactic.trace
                    "trace"
                    (str
                     "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\""))
                   (Tactic.traceMessage
                    "trace"
                    (str
                     "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\"")))
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)
                     ","
                     (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                    "]")
                   [])
                  []
                  (Tactic.exact
                   "exact"
                   (Term.app
                    (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `le_mul_dist)
                    [(Term.anonymousCtor "⟨" [`y' "," `y's] "⟩")
                     (Term.anonymousCtor "⟨" [`x' "," `x's] "⟩")]))]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               («term_*_»
                (Term.typeAscription
                 "("
                 («term_*_»
                  («term_*_»
                   (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
                   "*"
                   («term_⁻¹»
                    («term_-_»
                     («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                     "-"
                     `c)
                    "⁻¹"))
                  "*"
                  `c)
                 ":"
                 [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
                 ")")
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖»
                 "‖"
                 («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
                 "‖")))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `norm_sub_rev)
                     ","
                     (Tactic.simpLemma [] [] `Nonneg.coe_mul)]
                    "]"]
                   [])
                  []
                  (Mathlib.Tactic.RingNF.ring "ring")]))))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.intro "intro" [`x `hx `y `hy])
          []
          (Mathlib.Tactic.set
           "set"
           []
           (Mathlib.Tactic.setArgsRest
            `A
            []
            ":="
            (Term.app `hf.to_local_equiv [`hc])
            ["with" [] `hA]))
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`Af []]
             [(Term.typeSpec
               ":"
               (Term.forall "∀" [`z] [] "," («term_=_» (Term.app `A [`z]) "=" (Term.app `f [`z]))))]
             ":="
             (Term.fun "fun" (Term.basicFun [`z] [] "=>" `rfl)))))
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj
               (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
               "."
               (fieldIdx "1"))
              [`hx]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `x's)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget
             []
             (Term.app
              (Term.proj
               (Term.app `mem_image [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
               "."
               (fieldIdx "1"))
              [`hy]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y')])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y's)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Af [`x']))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] (Term.app `Af [`y']))
             ","
             (Tactic.rwRule [] (Term.app `A.left_inv [`x's]))
             ","
             (Tactic.rwRule [] (Term.app `A.left_inv [`y's]))]
            "]")
           [])
          []
          (calcTactic
           "calc"
           (calcStep
            («term_≤_»
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              («term_-_»
               («term_-_» `x' "-" `y')
               "-"
               (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))
              "‖")
             "≤"
             («term_*_»
              (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
              "*"
              (Analysis.Normed.Group.Basic.«term‖_‖»
               "‖"
               (Term.app
                `f'
                [(«term_-_»
                  («term_-_» `x' "-" `y')
                  "-"
                  (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))])
               "‖")))
            ":="
            (Term.app
             (Term.proj
              (Term.typeAscription
               "("
               `f'
               ":"
               [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
               ")")
              "."
              `bound_of_antilipschitz)
             [`f'.antilipschitz (Term.hole "_")]))
           [(calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_-_»
                 («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
                 "-"
                 (Term.app `f' [(«term_-_» `y' "-" `x')]))
                "‖")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.congr "congr" [(num "2")])
                 []
                 (Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `ContinuousLinearEquiv.apply_symm_apply)
                    ","
                    (Tactic.simpLemma [] [] `ContinuousLinearEquiv.map_sub)]
                   "]"]
                  [])
                 []
                 (Tactic.abel "abel" [] [])]))))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
               "*"
               («term_*_»
                `c
                "*"
                (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y' "-" `x') "‖"))))
             ":="
             (Term.app
              `mul_le_mul_of_nonneg_left
              [(Term.app `hf [(Term.hole "_") `y's (Term.hole "_") `x's])
               (Term.app `Nnreal.coe_nonneg [(Term.hole "_")])]))
            (calcStep
             («term_≤_»
              (Term.hole "_")
              "≤"
              («term_*_»
               (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
               "*"
               («term_*_»
                `c
                "*"
                («term_*_»
                 (Term.typeAscription
                  "("
                  («term_⁻¹»
                   («term_-_»
                    («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                    "-"
                    `c)
                   "⁻¹")
                  ":"
                  [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
                  ")")
                 "*"
                 (Analysis.Normed.Group.Basic.«term‖_‖»
                  "‖"
                  («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
                  "‖")))))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(choice
                  (Tactic.trace
                   "trace"
                   (str
                    "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\""))
                  (Tactic.traceMessage
                   "trace"
                   (str
                    "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\"")))
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)
                    ","
                    (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
                   "]")
                  [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `le_mul_dist)
                   [(Term.anonymousCtor "⟨" [`y' "," `y's] "⟩")
                    (Term.anonymousCtor "⟨" [`x' "," `x's] "⟩")]))]))))
            (calcStep
             («term_=_»
              (Term.hole "_")
              "="
              («term_*_»
               (Term.typeAscription
                "("
                («term_*_»
                 («term_*_»
                  (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
                  "*"
                  («term_⁻¹»
                   («term_-_»
                    («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                    "-"
                    `c)
                   "⁻¹"))
                 "*"
                 `c)
                ":"
                [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
                ")")
               "*"
               (Analysis.Normed.Group.Basic.«term‖_‖»
                "‖"
                («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
                "‖")))
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `norm_sub_rev)
                    ","
                    (Tactic.simpLemma [] [] `Nonneg.coe_mul)]
                   "]"]
                  [])
                 []
                 (Mathlib.Tactic.RingNF.ring "ring")]))))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_≤_»
         (Analysis.Normed.Group.Basic.«term‖_‖»
          "‖"
          («term_-_»
           («term_-_» `x' "-" `y')
           "-"
           (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))
          "‖")
         "≤"
         («term_*_»
          (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
          "*"
          (Analysis.Normed.Group.Basic.«term‖_‖»
           "‖"
           (Term.app
            `f'
            [(«term_-_»
              («term_-_» `x' "-" `y')
              "-"
              (Term.app `f'.symm [(«term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))]))])
           "‖")))
        ":="
        (Term.app
         (Term.proj
          (Term.typeAscription
           "("
           `f'
           ":"
           [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
           ")")
          "."
          `bound_of_antilipschitz)
         [`f'.antilipschitz (Term.hole "_")]))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_-_»
             («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
             "-"
             (Term.app `f' [(«term_-_» `y' "-" `x')]))
            "‖")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.congr "congr" [(num "2")])
             []
             (Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `ContinuousLinearEquiv.apply_symm_apply)
                ","
                (Tactic.simpLemma [] [] `ContinuousLinearEquiv.map_sub)]
               "]"]
              [])
             []
             (Tactic.abel "abel" [] [])]))))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
           "*"
           («term_*_»
            `c
            "*"
            (Analysis.Normed.Group.Basic.«term‖_‖» "‖" («term_-_» `y' "-" `x') "‖"))))
         ":="
         (Term.app
          `mul_le_mul_of_nonneg_left
          [(Term.app `hf [(Term.hole "_") `y's (Term.hole "_") `x's])
           (Term.app `Nnreal.coe_nonneg [(Term.hole "_")])]))
        (calcStep
         («term_≤_»
          (Term.hole "_")
          "≤"
          («term_*_»
           (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
           "*"
           («term_*_»
            `c
            "*"
            («term_*_»
             (Term.typeAscription
              "("
              («term_⁻¹»
               («term_-_»
                («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                "-"
                `c)
               "⁻¹")
              ":"
              [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
              ")")
             "*"
             (Analysis.Normed.Group.Basic.«term‖_‖»
              "‖"
              («term_-_» (Term.app `A [`y']) "-" (Term.app `A [`x']))
              "‖")))))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(choice
              (Tactic.trace
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\""))
              (Tactic.traceMessage
               "trace"
               (str
                "\"./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\\\"[\\\", expr mul_le_mul_of_nonneg_left, \\\",\\\", expr nnreal.coe_nonneg, \\\"]\\\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error\"")))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `dist_eq_norm)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `hf.antilipschitz [`hc]) "." `le_mul_dist)
               [(Term.anonymousCtor "⟨" [`y' "," `y's] "⟩")
                (Term.anonymousCtor "⟨" [`x' "," `x's] "⟩")]))]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Term.typeAscription
            "("
            («term_*_»
             («term_*_»
              (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
              "*"
              («term_⁻¹»
               («term_-_»
                («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
                "-"
                `c)
               "⁻¹"))
             "*"
             `c)
            ":"
            [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
            ")")
           "*"
           (Analysis.Normed.Group.Basic.«term‖_‖»
            "‖"
            («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
            "‖")))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `norm_sub_rev) "," (Tactic.simpLemma [] [] `Nonneg.coe_mul)]
               "]"]
              [])
             []
             (Mathlib.Tactic.RingNF.ring "ring")]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `norm_sub_rev) "," (Tactic.simpLemma [] [] `Nonneg.coe_mul)]
            "]"]
           [])
          []
          (Mathlib.Tactic.RingNF.ring "ring")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.RingNF.ring "ring")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `norm_sub_rev) "," (Tactic.simpLemma [] [] `Nonneg.coe_mul)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Nonneg.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `norm_sub_rev
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_»
        (Term.typeAscription
         "("
         («term_*_»
          («term_*_»
           (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
           "*"
           («term_⁻¹»
            («term_-_»
             («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
             "-"
             `c)
            "⁻¹"))
          "*"
          `c)
         ":"
         [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
         ")")
        "*"
        (Analysis.Normed.Group.Basic.«term‖_‖»
         "‖"
         («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
         "‖")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       (Term.typeAscription
        "("
        («term_*_»
         («term_*_»
          (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
          "*"
          («term_⁻¹»
           («term_-_»
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
            "-"
            `c)
           "⁻¹"))
         "*"
         `c)
        ":"
        [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
        ")")
       "*"
       (Analysis.Normed.Group.Basic.«term‖_‖»
        "‖"
        («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
        "‖"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Analysis.Normed.Group.Basic.«term‖_‖»
       "‖"
       («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
       "‖")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_-_» (Term.app `A [`x']) "-" (Term.app `A [`y']))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `A [`y'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      (Term.app `A [`x'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `A
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.typeAscription
       "("
       («term_*_»
        («term_*_»
         (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
         "*"
         («term_⁻¹»
          («term_-_»
           («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
           "-"
           `c)
          "⁻¹"))
        "*"
        `c)
       ":"
       [(Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Nnreal.Data.Real.Nnreal.nnreal "ℝ≥0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_*_»
        (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
        "*"
        («term_⁻¹»
         («term_-_»
          («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
          "-"
          `c)
         "⁻¹"))
       "*"
       `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_»
       (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
       "*"
       («term_⁻¹»
        («term_-_»
         («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
         "-"
         `c)
        "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹»
       («term_-_»
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
        "-"
        `c)
       "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_-_» («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹") "-" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The inverse function is approximated linearly on `f '' s` by `f'.symm`. -/
  theorem
    toInv
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      :
        ApproximatesLinearOn
          hf . toLocalEquiv hc . symm ( f' . symm : F →L[ 𝕜 ] E ) f '' s N * N ⁻¹ - c ⁻¹ * c
    :=
      by
        intro x hx y hy
          set A := hf.to_local_equiv hc with hA
          have Af : ∀ z , A z = f z := fun z => rfl
          rcases mem_image _ _ _ . 1 hx with ⟨ x' , x's , rfl ⟩
          rcases mem_image _ _ _ . 1 hy with ⟨ y' , y's , rfl ⟩
          rw [ ← Af x' , ← Af y' , A.left_inv x's , A.left_inv y's ]
          calc
            ‖ x' - y' - f'.symm A x' - A y' ‖ ≤ N * ‖ f' x' - y' - f'.symm A x' - A y' ‖
              :=
              ( f' : E →L[ 𝕜 ] F ) . bound_of_antilipschitz f'.antilipschitz _
            _ = N * ‖ A y' - A x' - f' y' - x' ‖
                :=
                by
                  congr 2
                    simp
                      only
                      [ ContinuousLinearEquiv.apply_symm_apply , ContinuousLinearEquiv.map_sub ]
                    abel
              _ ≤ N * c * ‖ y' - x' ‖
                :=
                mul_le_mul_of_nonneg_left hf _ y's _ x's Nnreal.coe_nonneg _
              _ ≤ N * c * ( N ⁻¹ - c ⁻¹ : ℝ≥0 ) * ‖ A y' - A x' ‖
                :=
                by
                  trace
                        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr mul_le_mul_of_nonneg_left, \",\", expr nnreal.coe_nonneg, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
                      trace
                        "./././Mathport/Syntax/Translate/Tactic/Builtin.lean:75:38: in apply_rules #[[\"[\", expr mul_le_mul_of_nonneg_left, \",\", expr nnreal.coe_nonneg, \"]\"], []]: ./././Mathport/Syntax/Translate/Basic.lean:349:22: unsupported: parse error"
                    rw [ ← dist_eq_norm , ← dist_eq_norm ]
                    exact hf.antilipschitz hc . le_mul_dist ⟨ y' , y's ⟩ ⟨ x' , x's ⟩
              _ = ( N * N ⁻¹ - c ⁻¹ * c : ℝ≥0 ) * ‖ A x' - A y' ‖
                :=
                by simp only [ norm_sub_rev , Nonneg.coe_mul ] ring
#align approximates_linear_on.to_inv ApproximatesLinearOn.toInv

include cs

section

variable (f s)

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "Given a function `f` that approximates a linear equivalence on an open set `s`,\nreturns a local homeomorph with `to_fun = f` and `source = s`. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toLocalHomeomorph [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `IsOpen [`s])] [] ")")]
       [(Term.typeSpec ":" (Term.app `LocalHomeomorph [`E `F]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `toLocalEquiv
           []
           []
           ":="
           (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc]))))
        []
        (Command.whereStructField (Term.letDecl (Term.letIdDecl `open_source [] [] ":=" `hs)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `open_target
           []
           []
           ":="
           (Term.app
            (Term.proj `hf "." `open_image)
            [(Term.proj `f' "." `toNonlinearRightInverse)
             `hs
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `f'.to_linear_equiv.to_equiv.subsingleton_congr)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])])))]))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl `continuous_to_fun [] [] ":=" (Term.proj `hf "." `ContinuousOn))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `continuous_inv_fun
           []
           []
           ":="
           (Term.app (Term.proj `hf "." `inverse_continuous_on) [`hc]))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `inverse_continuous_on) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `inverse_continuous_on)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `hf "." `ContinuousOn)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `hf "." `open_image)
       [(Term.proj `f' "." `toNonlinearRightInverse)
        `hs
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `f'.to_linear_equiv.to_equiv.subsingleton_congr)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `f'.to_linear_equiv.to_equiv.subsingleton_congr)]
            "]")
           [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `f'.to_linear_equiv.to_equiv.subsingleton_congr)]
        "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f'.to_linear_equiv.to_equiv.subsingleton_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0,
     tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(Std.Tactic.tacticRwa__
          "rwa"
          (Tactic.rwRuleSeq
           "["
           [(Tactic.rwRule [] `f'.to_linear_equiv.to_equiv.subsingleton_congr)]
           "]")
          [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])])))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f' "." `toNonlinearRightInverse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `open_image)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `toLocalEquiv) [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalEquiv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app `LocalHomeomorph [`E `F])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LocalHomeomorph
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsOpen [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
    Given a function `f` that approximates a linear equivalence on an open set `s`,
    returns a local homeomorph with `to_fun = f` and `source = s`. -/
  def
    toLocalHomeomorph
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c )
        ( hc : Subsingleton E ∨ c < N ⁻¹ )
        ( hs : IsOpen s )
      : LocalHomeomorph E F
    where
      toLocalEquiv := hf . toLocalEquiv hc
        open_source := hs
        open_target
          :=
          hf . open_image
            f' . toNonlinearRightInverse
              hs
              by rwa [ f'.to_linear_equiv.to_equiv.subsingleton_congr ] at hc
        continuous_to_fun := hf . ContinuousOn
        continuous_inv_fun := hf . inverse_continuous_on hc
#align approximates_linear_on.to_local_homeomorph ApproximatesLinearOn.toLocalHomeomorph

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "A function `f` that approximates a linear equivalence on the whole space is a homeomorphism. -/")]
      []
      []
      []
      []
      [])
     (Command.def
      "def"
      (Command.declId `toHomeomorph [])
      (Command.optDeclSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `univ
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")]
       [(Term.typeSpec ":" (Topology.Homeomorph.«term_≃ₜ_» `E " ≃ₜ " `F))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app
             (Term.proj
              (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
              "."
              `toHomeomorphOfSourceEqUnivTargetEqUniv)
             [`rfl (Term.hole "_")]))
           []
           (Tactic.change
            "change"
            («term_=_» (Set.Data.Set.Image.term_''_ `f " '' " `univ) "=" `univ)
            [])
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `image_univ) "," (Tactic.rwRule [] `range_iff_surjective)]
             "]")
            [])
           []
           (Tactic.exact "exact" (Term.app `hf.surjective [`hc]))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj
             (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
             "."
             `toHomeomorphOfSourceEqUnivTargetEqUniv)
            [`rfl (Term.hole "_")]))
          []
          (Tactic.change
           "change"
           («term_=_» (Set.Data.Set.Image.term_''_ `f " '' " `univ) "=" `univ)
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `image_univ) "," (Tactic.rwRule [] `range_iff_surjective)]
            "]")
           [])
          []
          (Tactic.exact "exact" (Term.app `hf.surjective [`hc]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `hf.surjective [`hc]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hf.surjective [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.surjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `image_univ) "," (Tactic.rwRule [] `range_iff_surjective)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `range_iff_surjective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `image_univ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_» (Set.Data.Set.Image.term_''_ `f " '' " `univ) "=" `univ)
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Set.Data.Set.Image.term_''_ `f " '' " `univ) "=" `univ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Data.Set.Image.term_''_ `f " '' " `univ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `univ
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj
         (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
         "."
         `toHomeomorphOfSourceEqUnivTargetEqUniv)
        [`rfl (Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
        "."
        `toHomeomorphOfSourceEqUnivTargetEqUniv)
       [`rfl (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
       "."
       `toHomeomorphOfSourceEqUnivTargetEqUniv)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `is_open_univ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hf.to_local_homeomorph
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `hf.to_local_homeomorph [(Term.hole "_") (Term.hole "_") `hc `is_open_univ])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Topology.Homeomorph.«term_≃ₜ_» `E " ≃ₜ " `F)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 26 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 26,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- A function `f` that approximates a linear equivalence on the whole space is a homeomorphism. -/
  def
    toHomeomorph
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) univ c ) ( hc : Subsingleton E ∨ c < N ⁻¹ )
      : E ≃ₜ F
    :=
      by
        refine'
            hf.to_local_homeomorph _ _ hc is_open_univ . toHomeomorphOfSourceEqUnivTargetEqUniv
              rfl _
          change f '' univ = univ
          rw [ image_univ , range_iff_surjective ]
          exact hf.surjective hc
#align approximates_linear_on.to_homeomorph ApproximatesLinearOn.toHomeomorph

omit cs

/-- In a real vector space, a function `f` that approximates a linear equivalence on a subset `s`
can be extended to a homeomorphism of the whole space. -/
theorem exists_homeomorph_extension {E : Type _} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type _} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {s : Set E}
    {f : E → F} {f' : E ≃L[ℝ] F} {c : ℝ≥0} (hf : ApproximatesLinearOn f (f' : E →L[ℝ] F) s c)
    (hc : Subsingleton E ∨ lipschitzExtensionConstant F * c < ‖(f'.symm : F →L[ℝ] E)‖₊⁻¹) :
    ∃ g : E ≃ₜ F, EqOn f g s :=
  by
  -- the difference `f - f'` is Lipschitz on `s`. It can be extended to a Lipschitz function `u`
  -- on the whole space, with a slightly worse Lipschitz constant. Then `f' + u` will be the
  -- desired homeomorphism.
  obtain ⟨u, hu, uf⟩ :
    ∃ u : E → F, LipschitzWith (lipschitzExtensionConstant F * c) u ∧ eq_on (f - f') u s :=
    hf.lipschitz_on_with.extend_finite_dimension
  let g : E → F := fun x => f' x + u x
  have fg : eq_on f g s := fun x hx => by simp_rw [g, ← uf hx, Pi.sub_apply, add_sub_cancel'_right]
  have hg : ApproximatesLinearOn g (f' : E →L[ℝ] F) univ (lipschitzExtensionConstant F * c) :=
    by
    apply LipschitzOnWith.approximatesLinearOn
    rw [lipschitz_on_univ]
    convert hu
    ext x
    simp only [add_sub_cancel', ContinuousLinearEquiv.coe_coe, Pi.sub_apply]
  haveI : FiniteDimensional ℝ E := f'.symm.to_linear_equiv.finite_dimensional
  exact ⟨hg.to_homeomorph g hc, fg⟩
#align
  approximates_linear_on.exists_homeomorph_extension ApproximatesLinearOn.exists_homeomorph_extension

end

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `to_local_homeomorph_coe [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `IsOpen [`s])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.typeAscription
          "("
          (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
          ":"
          [(Term.arrow `E "→" `F)]
          ")")
         "="
         `f)))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.typeAscription
        "("
        (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
        ":"
        [(Term.arrow `E "→" `F)]
        ")")
       "="
       `f)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.typeAscription
       "("
       (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
       ":"
       [(Term.arrow `E "→" `F)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `E "→" `F)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `F
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `E
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalHomeomorph)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsOpen [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_local_homeomorph_coe
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c )
        ( hc : Subsingleton E ∨ c < N ⁻¹ )
        ( hs : IsOpen s )
      : ( hf . toLocalHomeomorph f s hc hs : E → F ) = f
    := rfl
#align approximates_linear_on.to_local_homeomorph_coe ApproximatesLinearOn.to_local_homeomorph_coe

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `to_local_homeomorph_source [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `IsOpen [`s])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `source)
         "="
         `s)))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `source)
       "="
       `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `source)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalHomeomorph)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsOpen [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_local_homeomorph_source
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c )
        ( hc : Subsingleton E ∨ c < N ⁻¹ )
        ( hs : IsOpen s )
      : hf . toLocalHomeomorph f s hc hs . source = s
    := rfl
#align
  approximates_linear_on.to_local_homeomorph_source ApproximatesLinearOn.to_local_homeomorph_source

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes "@[" [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))] "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `to_local_homeomorph_target [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `IsOpen [`s])] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `target)
         "="
         (Set.Data.Set.Image.term_''_ `f " '' " `s))))
      (Command.declValSimple ":=" `rfl [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `target)
       "="
       (Set.Data.Set.Image.term_''_ `f " '' " `s))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_ `f " '' " `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `target)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalHomeomorph)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `IsOpen [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `IsOpen
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'ident'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.hole'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∨_»
       (Term.app `Subsingleton [`E])
       "∨"
       («term_<_»
        `c
        "<"
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `c "<" («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicitBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp ]
  theorem
    to_local_homeomorph_target
    ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c )
        ( hc : Subsingleton E ∨ c < N ⁻¹ )
        ( hs : IsOpen s )
      : hf . toLocalHomeomorph f s hc hs . target = f '' s
    := rfl
#align
  approximates_linear_on.to_local_homeomorph_target ApproximatesLinearOn.to_local_homeomorph_target

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `closed_ball_subset_target [])
      (Command.declSig
       [(Term.explicitBinder
         "("
         [`hf]
         [":"
          (Term.app
           `ApproximatesLinearOn
           [`f
            (Term.typeAscription
             "("
             `f'
             ":"
             [(Topology.Algebra.Module.Basic.«term_→L[_]_» `E " →L[" `𝕜 "] " `F)]
             ")")
            `s
            `c])]
         []
         ")")
        (Term.explicitBinder
         "("
         [`hc]
         [":"
          («term_∨_»
           (Term.app `Subsingleton [`E])
           "∨"
           («term_<_»
            `c
            "<"
            («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")))]
         []
         ")")
        (Term.explicitBinder "(" [`hs] [":" (Term.app `IsOpen [`s])] [] ")")
        (Term.implicitBinder "{" [`b] [":" `E] "}")
        (Term.explicitBinder "(" [`ε0] [":" («term_≤_» (num "0") "≤" `ε)] [] ")")
        (Term.explicitBinder
         "("
         [`hε]
         [":" («term_⊆_» (Term.app `closedBall [`b `ε]) "⊆" `s)]
         []
         ")")]
       (Term.typeSpec
        ":"
        («term_⊆_»
         (Term.app
          `closedBall
          [(Term.app `f [`b])
           («term_*_»
            («term_-_»
             («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
             "-"
             `c)
            "*"
            `ε)])
         "⊆"
         (Term.proj
          (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
          "."
          `target))))
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj
         (Term.app
          (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
          [(Term.proj `f' "." `toNonlinearRightInverse) `ε0 `hε])
         "."
         `mono)
        [`hε (Term.app `Subset.refl [(Term.hole "_")])])
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        (Term.app
         (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
         [(Term.proj `f' "." `toNonlinearRightInverse) `ε0 `hε])
        "."
        `mono)
       [`hε (Term.app `Subset.refl [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Subset.refl [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Subset.refl
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Subset.refl [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       (Term.app
        (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
        [(Term.proj `f' "." `toNonlinearRightInverse) `ε0 `hε])
       "."
       `mono)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
       [(Term.proj `f' "." `toNonlinearRightInverse) `ε0 `hε])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hε
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ε0
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `f' "." `toNonlinearRightInverse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.proj `hf "." `surj_on_closed_ball_of_nonlinear_right_inverse)
      [(Term.proj `f' "." `toNonlinearRightInverse) `ε0 `hε])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_⊆_»
       (Term.app
        `closedBall
        [(Term.app `f [`b])
         («term_*_»
          («term_-_»
           («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
           "-"
           `c)
          "*"
          `ε)])
       "⊆"
       (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `target))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs]) "." `target)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hc
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `hf "." `toLocalHomeomorph)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hf
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app (Term.proj `hf "." `toLocalHomeomorph) [`f `s `hc `hs])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `closedBall
       [(Term.app `f [`b])
        («term_*_»
         («term_-_»
          («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
          "-"
          `c)
         "*"
         `ε)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_»
       («term_-_»
        («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
        "-"
        `c)
       "*"
       `ε)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ε
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_-_» («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹") "-" `c)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `c
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
      («term_⁻¹» (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N") "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (ApproximatesLinearOn.Analysis.Calculus.Inverse.termN "N")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN', expected 'ApproximatesLinearOn.Analysis.Calculus.Inverse.termN._@.Analysis.Calculus.Inverse._hyg.13'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  closed_ball_subset_target
  ( hf : ApproximatesLinearOn f ( f' : E →L[ 𝕜 ] F ) s c )
      ( hc : Subsingleton E ∨ c < N ⁻¹ )
      ( hs : IsOpen s )
      { b : E }
      ( ε0 : 0 ≤ ε )
      ( hε : closedBall b ε ⊆ s )
    : closedBall f b N ⁻¹ - c * ε ⊆ hf . toLocalHomeomorph f s hc hs . target
  :=
    hf . surj_on_closed_ball_of_nonlinear_right_inverse f' . toNonlinearRightInverse ε0 hε . mono
      hε Subset.refl _
#align
  approximates_linear_on.closed_ball_subset_target ApproximatesLinearOn.closed_ball_subset_target

end ApproximatesLinearOn

/-!
### Inverse function theorem

Now we prove the inverse function theorem. Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `approximates_linear_on` on an open neighborhood
of `a`, and we can apply `approximates_linear_on.to_local_homeomorph` to construct the inverse
function. -/


namespace HasStrictFderivAt

/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFderivAt f f' a) {c : ℝ≥0} (hc : Subsingleton E ∨ 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
  by
  cases' hc with hE hc
  · refine' ⟨univ, IsOpen.mem_nhds is_open_univ trivial, fun x hx y hy => _⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩
#align has_strict_fderiv_at.approximates_deriv_on_nhds HasStrictFderivAt.approximates_deriv_on_nhds

theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) (h : LinearMap.range f' = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) :=
  by
  let f'symm := f'.nonlinear_right_inverse_of_surjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinear_right_inverse_of_surjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, Nnreal.half_pos, Nnreal.inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (Nnreal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]
#align has_strict_fderiv_at.map_nhds_eq_of_surj HasStrictFderivAt.map_nhds_eq_of_surj

variable [cs : CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

theorem approximates_deriv_on_open_nhds (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∃ (s : Set E)(hs : a ∈ s ∧ IsOpen s),
      ApproximatesLinearOn f (f' : E →L[𝕜] F) s (‖(f'.symm : F →L[𝕜] E)‖₊⁻¹ / 2) :=
  by
  refine' ((nhds_basis_opens a).exists_iff _).1 _
  exact fun s t => ApproximatesLinearOn.monoSet
  exact
    hf.approximates_deriv_on_nhds <|
      (f'.subsingleton_or_nnnorm_symm_pos.imp id) fun hf' =>
        Nnreal.half_pos <| Nnreal.inv_pos.2 <| hf'
#align
  has_strict_fderiv_at.approximates_deriv_on_open_nhds HasStrictFderivAt.approximates_deriv_on_open_nhds

include cs

variable (f)

/-- Given a function with an invertible strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `has_strict_fderiv_at.to_local_inverse` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def toLocalHomeomorph (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : LocalHomeomorph E F :=
  ApproximatesLinearOn.toLocalHomeomorph f (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).snd
    ((f'.subsingleton_or_nnnorm_symm_pos.imp id) fun hf' =>
      Nnreal.half_lt_self <| ne_of_gt <| Nnreal.inv_pos.2 <| hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).fst.2
#align has_strict_fderiv_at.to_local_homeomorph HasStrictFderivAt.toLocalHomeomorph

variable {f}

@[simp]
theorem to_local_homeomorph_coe (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    (hf.toLocalHomeomorph f : E → F) = f :=
  rfl
#align has_strict_fderiv_at.to_local_homeomorph_coe HasStrictFderivAt.to_local_homeomorph_coe

theorem mem_to_local_homeomorph_source (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    a ∈ (hf.toLocalHomeomorph f).source :=
  (Classical.choose_spec hf.approximates_deriv_on_open_nhds).fst.1
#align
  has_strict_fderiv_at.mem_to_local_homeomorph_source HasStrictFderivAt.mem_to_local_homeomorph_source

theorem image_mem_to_local_homeomorph_target (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    f a ∈ (hf.toLocalHomeomorph f).target :=
  (hf.toLocalHomeomorph f).map_source hf.mem_to_local_homeomorph_source
#align
  has_strict_fderiv_at.image_mem_to_local_homeomorph_target HasStrictFderivAt.image_mem_to_local_homeomorph_target

theorem map_nhds_eq_of_equiv (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toLocalHomeomorph f).map_nhds_eq hf.mem_to_local_homeomorph_source
#align has_strict_fderiv_at.map_nhds_eq_of_equiv HasStrictFderivAt.map_nhds_eq_of_equiv

variable (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def localInverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.toLocalHomeomorph f).symm
#align has_strict_fderiv_at.local_inverse HasStrictFderivAt.localInverse

variable {f f' a}

theorem local_inverse_def (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toLocalHomeomorph f).symm :=
  rfl
#align has_strict_fderiv_at.local_inverse_def HasStrictFderivAt.local_inverse_def

theorem eventually_left_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toLocalHomeomorph f).eventually_left_inverse hf.mem_to_local_homeomorph_source
#align has_strict_fderiv_at.eventually_left_inverse HasStrictFderivAt.eventually_left_inverse

@[simp]
theorem local_inverse_apply_image (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds
#align has_strict_fderiv_at.local_inverse_apply_image HasStrictFderivAt.local_inverse_apply_image

theorem eventually_right_inverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toLocalHomeomorph f).eventually_right_inverse' hf.mem_to_local_homeomorph_source
#align has_strict_fderiv_at.eventually_right_inverse HasStrictFderivAt.eventually_right_inverse

theorem local_inverse_continuous_at (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toLocalHomeomorph f).continuous_at_symm hf.image_mem_to_local_homeomorph_target
#align
  has_strict_fderiv_at.local_inverse_continuous_at HasStrictFderivAt.local_inverse_continuous_at

theorem local_inverse_tendsto (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toLocalHomeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source
#align has_strict_fderiv_at.local_inverse_tendsto HasStrictFderivAt.local_inverse_tendsto

theorem local_inverse_unique (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : ∀ᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
  eventually_eq_of_left_inv_of_right_inv hg hf.eventually_right_inverse <|
    (hf.toLocalHomeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source
#align has_strict_fderiv_at.local_inverse_unique HasStrictFderivAt.local_inverse_unique

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem toLocalInverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFderivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.toLocalHomeomorph f).hasStrictFderivAtSymm hf.image_mem_to_local_homeomorph_target <| by
    simpa [← local_inverse_def] using hf
#align has_strict_fderiv_at.to_local_inverse HasStrictFderivAt.toLocalInverse

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[complete_space E]`
see `of_local_left_inverse`.  -/
theorem toLocalLeftInverse (hf : HasStrictFderivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictFderivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.toLocalInverse.congr_of_eventually_eq <| (hf.local_inverse_unique hg).mono fun _ => Eq.symm
#align has_strict_fderiv_at.to_local_left_inverse HasStrictFderivAt.toLocalLeftInverse

end HasStrictFderivAt

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_fderiv_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
    (hf : ∀ x, HasStrictFderivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge
#align open_map_of_strict_fderiv_equiv open_map_of_strict_fderiv_equiv

/-!
### Inverse function theorem, 1D case

In this case we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `continuous_linear_equiv.units_equiv_aut` to translate `has_strict_deriv_at f f' a` and
`f' ≠ 0` into `has_strict_fderiv_at f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/


namespace HasStrictDerivAt

variable [cs : CompleteSpace 𝕜] {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)

include cs

variable (f f' a)

/-- A function that is inverse to `f` near `a`. -/
@[reducible]
def localInverse : 𝕜 → 𝕜 :=
  (hf.hasStrictFderivAtEquiv hf').localInverse _ _ _
#align has_strict_deriv_at.local_inverse HasStrictDerivAt.localInverse

variable {f f' a}

theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.hasStrictFderivAtEquiv hf').map_nhds_eq_of_equiv
#align has_strict_deriv_at.map_nhds_eq HasStrictDerivAt.map_nhds_eq

theorem to_local_inverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.hasStrictFderivAtEquiv hf').toLocalInverse
#align has_strict_deriv_at.to_local_inverse HasStrictDerivAt.to_local_inverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
    HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.hasStrictFderivAtEquiv hf').toLocalLeftInverse hg
#align has_strict_deriv_at.to_local_left_inverse HasStrictDerivAt.to_local_left_inverse

end HasStrictDerivAt

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
theorem open_map_of_strict_deriv [CompleteSpace 𝕜] {f f' : 𝕜 → 𝕜}
    (hf : ∀ x, HasStrictDerivAt f (f' x) x) (h0 : ∀ x, f' x ≠ 0) : IsOpenMap f :=
  is_open_map_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge
#align open_map_of_strict_deriv open_map_of_strict_deriv

/-!
### Inverse function theorem, smooth case

-/


namespace ContDiffAt

variable {𝕂 : Type _} [IsROrC 𝕂]

variable {E' : Type _} [NormedAddCommGroup E'] [NormedSpace 𝕂 E']

variable {F' : Type _} [NormedAddCommGroup F'] [NormedSpace 𝕂 F']

variable [CompleteSpace E'] (f : E' → F') {f' : E' ≃L[𝕂] F'} {a : E'}

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `local_homeomorph` with `to_fun = f` and `a ∈ source`. -/
def toLocalHomeomorph {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : LocalHomeomorph E' F' :=
  (hf.hasStrictFderivAt' hf' hn).toLocalHomeomorph f
#align cont_diff_at.to_local_homeomorph ContDiffAt.toLocalHomeomorph

variable {f}

@[simp]
theorem to_local_homeomorph_coe {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) :
    (hf.toLocalHomeomorph f hf' hn : E' → F') = f :=
  rfl
#align cont_diff_at.to_local_homeomorph_coe ContDiffAt.to_local_homeomorph_coe

theorem mem_to_local_homeomorph_source {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) :
    a ∈ (hf.toLocalHomeomorph f hf' hn).source :=
  (hf.hasStrictFderivAt' hf' hn).mem_to_local_homeomorph_source
#align cont_diff_at.mem_to_local_homeomorph_source ContDiffAt.mem_to_local_homeomorph_source

theorem image_mem_to_local_homeomorph_target {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) :
    f a ∈ (hf.toLocalHomeomorph f hf' hn).target :=
  (hf.hasStrictFderivAt' hf' hn).image_mem_to_local_homeomorph_target
#align
  cont_diff_at.image_mem_to_local_homeomorph_target ContDiffAt.image_mem_to_local_homeomorph_target

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def localInverse {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a) (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a)
    (hn : 1 ≤ n) : F' → E' :=
  (hf.hasStrictFderivAt' hf' hn).localInverse f f' a
#align cont_diff_at.local_inverse ContDiffAt.localInverse

theorem local_inverse_apply_image {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFderivAt' hf' hn).local_inverse_apply_image
#align cont_diff_at.local_inverse_apply_image ContDiffAt.local_inverse_apply_image

/-- Given a `cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `cont_diff.to_local_homeomorph`) is
also `cont_diff`. -/
theorem to_local_inverse {n : ℕ∞} (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFderivAt f (f' : E' →L[𝕂] F') a) (hn : 1 ≤ n) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) :=
  by
  have := hf.local_inverse_apply_image hf' hn
  apply
    (hf.to_local_homeomorph f hf' hn).cont_diff_at_symm
      (image_mem_to_local_homeomorph_target hf hf' hn)
  · convert hf'
  · convert hf
#align cont_diff_at.to_local_inverse ContDiffAt.to_local_inverse

end ContDiffAt

