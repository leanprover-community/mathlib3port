/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel

! This file was ported from Lean 3 source module analysis.calculus.bump_function_findim
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Calculus.SpecificFunctions
import Mathbin.Analysis.Calculus.Series
import Mathbin.Analysis.Convolution
import Mathbin.Data.Set.Pointwise.Support

/-!
# Bump functions in finite-dimensional vector spaces

Let `E` be a finite-dimensional real normed vector space. We show that any open set `s` in `E` is
exactly the support of a smooth function taking values in `[0, 1]`,
in `is_open.exists_smooth_support_eq`.

TODO: use this construction to construct bump functions with nice behavior in any finite-dimensional
real normed vector space, by convolving the indicator function of `closed_ball 0 1` with a
function as above with `s = ball 0 D`.
-/


noncomputable section

open
  Set Metric TopologicalSpace Function Asymptotics MeasureTheory FiniteDimensional ContinuousLinearMap Filter MeasureTheory.Measure

open Pointwise TopologicalSpace Nnreal BigOperators convolution

variable {E : Type _} [NormedAddCommGroup E]

section

variable [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- If a set `s` is a neighborhood of `x`, then there exists a smooth function `f` taking
values in `[0, 1]`, supported in `s` and with `f x = 1`. -/
theorem exists_smooth_tsupport_subset {s : Set E} {x : E} (hs : s ∈ 𝓝 x) :
    ∃ f : E → ℝ,
      tsupport f ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1 ∧ f x = 1 :=
  by 
  obtain ⟨d, d_pos, hd⟩ : ∃ (d : ℝ)(hr : 0 < d), Euclidean.closedBall x d ⊆ s
  exact euclidean.nhds_basis_closed_ball.mem_iff.1 hs
  let c : ContDiffBumpOfInner (toEuclidean x) :=
    { R := d / 2
      r := d
      r_pos := half_pos d_pos
      r_lt_R := half_lt_self d_pos }
  let f : E → ℝ := c ∘ toEuclidean
  have f_supp : f.support ⊆ Euclidean.ball x d := by
    intro y hy
    have : toEuclidean y ∈ Function.support c := by
      simpa only [f, Function.mem_support, Function.comp_apply, Ne.def] using hy
    rwa [c.support_eq] at this
  have f_tsupp : tsupport f ⊆ Euclidean.closedBall x d := by
    rw [tsupport, ← Euclidean.closure_ball _ d_pos.ne']
    exact closure_mono f_supp
  refine' ⟨f, f_tsupp.trans hd, _, _, _, _⟩
  · refine' is_compact_of_is_closed_bounded is_closed_closure _
    have : bounded (Euclidean.closedBall x d) := euclidean.is_compact_closed_ball.bounded
    apply this.mono _
    refine' (IsClosed.closure_subset_iff Euclidean.is_closed_closed_ball).2 _
    exact f_supp.trans Euclidean.ball_subset_closed_ball
  · apply c.cont_diff.comp
    exact ContinuousLinearEquiv.contDiff _
  · rintro t ⟨y, rfl⟩
    exact ⟨c.nonneg, c.le_one⟩
  · apply c.one_of_mem_closed_ball
    apply mem_closed_ball_self
    exact (half_pos d_pos).le
#align exists_smooth_tsupport_subset exists_smooth_tsupport_subset

/-- Given an open set `s` in a finite-dimensional real normed vector space, there exists a smooth
function with values in `[0, 1]` whose support is exactly `s`. -/
theorem IsOpen.exists_smooth_support_eq {s : Set E} (hs : IsOpen s) :
    ∃ f : E → ℝ, f.support = s ∧ ContDiff ℝ ⊤ f ∧ Set.range f ⊆ Set.Icc 0 1 :=
  by
  /- For any given point `x` in `s`, one can construct a smooth function with support in `s` and
    nonzero at `x`. By second-countability, it follows that we may cover `s` with the supports of
    countably many such functions, say `g i`.
    Then `∑ i, r i • g i` will be the desired function if `r i` is a sequence of positive numbers
    tending quickly enough to zero. Indeed, this ensures that, for any `k ≤ i`, the `k`-th derivative
    of `r i • g i` is bounded by a prescribed (summable) sequence `u i`. From this, the summability
    of the series and of its successive derivatives follows. -/
  rcases eq_empty_or_nonempty s with (rfl | h's)
  ·
    exact
      ⟨fun x => 0, Function.support_zero, contDiffConst, by
        simp only [range_const, singleton_subset_iff, left_mem_Icc, zero_le_one]⟩
  let ι := { f : E → ℝ // f.support ⊆ s ∧ HasCompactSupport f ∧ ContDiff ℝ ⊤ f ∧ range f ⊆ Icc 0 1 }
  obtain ⟨T, T_count, hT⟩ : ∃ T : Set ι, T.Countable ∧ (⋃ f ∈ T, support (f : E → ℝ)) = s := by
    have : (⋃ f : ι, (f : E → ℝ).support) = s := by
      refine' subset.antisymm (Union_subset fun f => f.2.1) _
      intro x hx
      rcases exists_smooth_tsupport_subset (hs.mem_nhds hx) with ⟨f, hf⟩
      let g : ι := ⟨f, (subset_tsupport f).trans hf.1, hf.2.1, hf.2.2.1, hf.2.2.2.1⟩
      have : x ∈ support (g : E → ℝ) := by
        simp only [hf.2.2.2.2, Subtype.coe_mk, mem_support, Ne.def, one_ne_zero, not_false_iff]
      exact mem_Union_of_mem _ this
    simp_rw [← this]
    apply is_open_Union_countable
    rintro ⟨f, hf⟩
    exact hf.2.2.1.Continuous.is_open_support
  obtain ⟨g0, hg⟩ : ∃ g0 : ℕ → ι, T = range g0 := by
    apply countable.exists_eq_range T_count
    rcases eq_empty_or_nonempty T with (rfl | hT)
    · simp only [Union_false, Union_empty] at hT
      simp only [← hT, not_nonempty_empty] at h's
      exact h's.elim
    · exact hT
  let g : ℕ → E → ℝ := fun n => (g0 n).1
  have g_s : ∀ n, support (g n) ⊆ s := fun n => (g0 n).2.1
  have s_g : ∀ x ∈ s, ∃ n, x ∈ support (g n) := by
    intro x hx
    rw [← hT] at hx
    obtain ⟨i, iT, hi⟩ : ∃ (i : ι)(hi : i ∈ T), x ∈ support (i : E → ℝ) := by
      simpa only [mem_Union] using hx
    rw [hg, mem_range] at iT
    rcases iT with ⟨n, hn⟩
    rw [← hn] at hi
    exact ⟨n, hi⟩
  have g_smooth : ∀ n, ContDiff ℝ ⊤ (g n) := fun n => (g0 n).2.2.2.1
  have g_comp_supp : ∀ n, HasCompactSupport (g n) := fun n => (g0 n).2.2.1
  have g_nonneg : ∀ n x, 0 ≤ g n x := fun n x => ((g0 n).2.2.2.2 (mem_range_self x)).1
  obtain ⟨δ, δpos, c, δc, c_lt⟩ :
    ∃ δ : ℕ → ℝ≥0, (∀ i : ℕ, 0 < δ i) ∧ ∃ c : Nnreal, HasSum δ c ∧ c < 1
  exact Nnreal.exists_pos_sum_of_countable one_ne_zero ℕ
  have : ∀ n : ℕ, ∃ r : ℝ, 0 < r ∧ ∀ i ≤ n, ∀ x, ‖iteratedFderiv ℝ i (r • g n) x‖ ≤ δ n := by
    intro n
    have : ∀ i, ∃ R, ∀ x, ‖iteratedFderiv ℝ i (fun x => g n x) x‖ ≤ R := by
      intro i
      have : BddAbove (range fun x => ‖iteratedFderiv ℝ i (fun x : E => g n x) x‖) := by
        apply
          ((g_smooth n).continuous_iterated_fderiv
                le_top).norm.bdd_above_range_of_has_compact_support
        apply HasCompactSupport.comp_left _ norm_zero
        apply (g_comp_supp n).iteratedFderiv
      rcases this with ⟨R, hR⟩
      exact ⟨R, fun x => hR (mem_range_self _)⟩
    choose R hR using this
    let M := max (((Finset.range (n + 1)).image R).max' (by simp)) 1
    have M_pos : 0 < M := zero_lt_one.trans_le (le_max_right _ _)
    have δnpos : 0 < δ n := δpos n
    have IR : ∀ i ≤ n, R i ≤ M := by 
      intro i hi
      refine' le_trans _ (le_max_left _ _)
      apply Finset.le_max'
      apply Finset.mem_image_of_mem
      simp only [Finset.mem_range]
      linarith
    refine' ⟨M⁻¹ * δ n, by positivity, fun i hi x => _⟩
    calc
      ‖iteratedFderiv ℝ i ((M⁻¹ * δ n) • g n) x‖ = ‖(M⁻¹ * δ n) • iteratedFderiv ℝ i (g n) x‖ := by
        rw [iterated_fderiv_const_smul_apply]
        exact (g_smooth n).of_le le_top
      _ = M⁻¹ * δ n * ‖iteratedFderiv ℝ i (g n) x‖ := by
        rw [norm_smul, Real.norm_of_nonneg]
        positivity
      _ ≤ M⁻¹ * δ n * M := mul_le_mul_of_nonneg_left ((hR i x).trans (IR i hi)) (by positivity)
      _ = δ n := by field_simp [M_pos.ne']
      
  choose r rpos hr using this
  have S : ∀ x, Summable fun n => (r n • g n) x := by
    intro x
    refine' summable_of_nnnorm_bounded _ δc.summable fun n => _
    rw [← Nnreal.coe_le_coe, coe_nnnorm]
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) x
  refine' ⟨fun x => ∑' n, (r n • g n) x, _, _, _⟩
  · apply subset.antisymm
    · intro x hx
      simp only [Pi.smul_apply, Algebra.id.smul_eq_mul, mem_support, Ne.def] at hx
      contrapose! hx
      have : ∀ n, g n x = 0 := by 
        intro n
        contrapose! hx
        exact g_s n hx
      simp only [this, mul_zero, tsum_zero]
    · intro x hx
      obtain ⟨n, hn⟩ : ∃ n, x ∈ support (g n)
      exact s_g x hx
      have I : 0 < r n * g n x := mul_pos (rpos n) (lt_of_le_of_ne (g_nonneg n x) (Ne.symm hn))
      exact ne_of_gt (tsum_pos (S x) (fun i => mul_nonneg (rpos i).le (g_nonneg i x)) n I)
  · refine'
      contDiffTsumOfEventually (fun n => (g_smooth n).const_smul _)
        (fun k hk => (Nnreal.has_sum_coe.2 δc).Summable) _
    intro i hi
    simp only [Nat.cofinite_eq_at_top, Pi.smul_apply, Algebra.id.smul_eq_mul,
      Filter.eventually_at_top, ge_iff_le]
    exact ⟨i, fun n hn x => hr _ _ hn _⟩
  · rintro - ⟨y, rfl⟩
    refine' ⟨tsum_nonneg fun n => mul_nonneg (rpos n).le (g_nonneg n y), le_trans _ c_lt.le⟩
    have A : HasSum (fun n => (δ n : ℝ)) c := Nnreal.has_sum_coe.2 δc
    rw [← A.tsum_eq]
    apply tsum_le_tsum _ (S y) A.summable
    intro n
    apply (le_abs_self _).trans
    simpa only [norm_iterated_fderiv_zero] using hr n 0 (zero_le n) y
#align is_open.exists_smooth_support_eq IsOpen.exists_smooth_support_eq

end

