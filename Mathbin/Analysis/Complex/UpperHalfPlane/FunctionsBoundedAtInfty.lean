/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
import Mathbin.Algebra.Module.Submodule.Basic
import Mathbin.Analysis.Complex.UpperHalfPlane.Basic
import Mathbin.Order.Filter.ZeroAndBoundedAtFilter

/-!
# Bounded at infinity

For complex valued functions on the upper half plane, this file defines the filter `at_im_infty`
required for defining when functions are bounded at infinity and zero at infinity.
Both of which are relevant for defining modular forms.

-/


open Complex Filter

open TopologicalSpace UpperHalfPlane

noncomputable section

namespace UpperHalfPlane

/-- Filter for approaching `i∞`. -/
def atImInfty :=
  Filter.atTop.comap UpperHalfPlane.im

theorem at_im_infty_basis : atImInfty.HasBasis (fun _ => True) fun i : ℝ => im ⁻¹' Set.IciCat i :=
  Filter.HasBasis.comap UpperHalfPlane.im Filter.at_top_basis

theorem at_im_infty_mem (S : Set ℍ) : S ∈ at_im_infty ↔ ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → z ∈ S := by
  simp only [at_im_infty, Filter.mem_comap', Filter.mem_at_top_sets, ge_iff_le, Set.mem_set_of_eq,
    UpperHalfPlane.coe_im]
  refine' ⟨fun ⟨a, h⟩ => ⟨a, fun z hz => h (im z) hz rfl⟩, _⟩
  rintro ⟨A, h⟩
  refine' ⟨A, fun b hb x hx => h x _⟩
  rwa [hx]

/-- A function ` f : ℍ → α` is bounded at infinity if it is bounded along `at_im_infty`. -/
def IsBoundedAtImInfty {α : Type _} [HasNorm α] [One (ℍ → α)] (f : ℍ → α) : Prop :=
  BoundedAtFilter atImInfty f

/-- A function ` f : ℍ → α` is zero at infinity it is zero along `at_im_infty`. -/
def IsZeroAtImInfty {α : Type _} [Zero α] [TopologicalSpace α] (f : ℍ → α) : Prop :=
  ZeroAtFilter atImInfty f

theorem zero_form_is_bounded_at_im_infty {α : Type _} [NormedField α] : IsBoundedAtImInfty (0 : ℍ → α) :=
  zero_is_bounded_at_filter atImInfty

/-- Module of functions that are zero at infinity. -/
def zeroAtImInftySubmodule (α : Type _) [NormedField α] : Submodule α (ℍ → α) :=
  zeroAtFilterSubmodule atImInfty

/-- ubalgebra of functions that are bounded at infinity. -/
def boundedAtImInftySubalgebra (α : Type _) [NormedField α] : Subalgebra α (ℍ → α) :=
  boundedFilterSubalgebra atImInfty

theorem prod_of_bounded_is_bounded {f g : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (hg : IsBoundedAtImInfty g) :
    IsBoundedAtImInfty (f * g) := by simpa only [Pi.one_apply, mul_one, norm_eq_abs] using hf.mul hg

@[simp]
theorem bounded_mem (f : ℍ → ℂ) : IsBoundedAtImInfty f ↔ ∃ M A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ M := by
  simp [is_bounded_at_im_infty, bounded_at_filter, Asymptotics.is_O_iff, Filter.Eventually, at_im_infty_mem]

theorem zero_at_im_infty (f : ℍ → ℂ) :
    IsZeroAtImInfty f ↔ ∀ ε : ℝ, 0 < ε → ∃ A : ℝ, ∀ z : ℍ, A ≤ im z → abs (f z) ≤ ε := by
  rw [is_zero_at_im_infty, zero_at_filter, tendsto_iff_forall_eventually_mem]
  constructor
  · simp_rw [Filter.Eventually, at_im_infty_mem]
    intro h ε hε
    simpa using h (Metric.ClosedBall (0 : ℂ) ε) (Metric.closed_ball_mem_nhds (0 : ℂ) hε)
    
  · simp_rw [Metric.mem_nhds_iff]
    intro h s hs
    simp_rw [Filter.Eventually, at_im_infty_mem]
    obtain ⟨ε, h1, h2⟩ := hs
    have h11 : 0 < ε / 2 := by linarith
    obtain ⟨A, hA⟩ := h (ε / 2) h11
    use A
    intro z hz
    have hzs : f z ∈ s := by
      apply h2
      simp only [mem_ball_zero_iff, norm_eq_abs]
      apply lt_of_le_of_lt (hA z hz)
      linarith
    apply hzs
    

end UpperHalfPlane

