/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.complex.log_deriv
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.SpecialFunctions.Complex.Log
import Mathbin.Analysis.SpecialFunctions.ExpDeriv

/-!
# Differentiability of the complex `log` function

-/


noncomputable section

namespace Complex

open Set Filter

open Real Topology

/-- `complex.exp` as a `local_homeomorph` with `source = {z | -π < im z < π}` and
`target = {z | 0 < re z} ∪ {z | im z ≠ 0}`. This definition is used to prove that `complex.log`
is complex differentiable at all points but the negative real semi-axis. -/
def expLocalHomeomorph : LocalHomeomorph ℂ ℂ :=
  LocalHomeomorph.ofContinuousOpen
    { toFun := exp
      invFun := log
      source := { z : ℂ | z.im ∈ Ioo (-π) π }
      target := { z : ℂ | 0 < z.re } ∪ { z : ℂ | z.im ≠ 0 }
      map_source' := by
        rintro ⟨x, y⟩ ⟨h₁ : -π < y, h₂ : y < π⟩
        refine' (not_or_of_imp fun hz => _).symm
        obtain rfl : y = 0 := by
          rw [exp_im] at hz
          simpa [(Real.exp_pos _).ne', Real.sin_eq_zero_iff_of_lt_of_lt h₁ h₂] using hz
        rw [mem_setOf_eq, ← of_real_def, exp_of_real_re]
        exact Real.exp_pos x
      map_target' := fun z h =>
        suffices 0 ≤ z.re ∨ z.im ≠ 0 by
          simpa [log_im, neg_pi_lt_arg, (arg_le_pi _).lt_iff_ne, arg_eq_pi_iff, not_and_or]
        h.imp (fun h => le_of_lt h) id
      left_inv' := fun x hx => log_exp hx.1 (le_of_lt hx.2)
      right_inv' := fun x hx =>
        exp_log <| by
          rintro rfl
          simpa [lt_irrefl] using hx }
    continuous_exp.continuousOn isOpenMap_exp (isOpen_Ioo.preimage continuous_im)
#align complex.exp_local_homeomorph Complex.expLocalHomeomorph

theorem hasStrictDerivAt_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x ≠ 0 := by
    rintro rfl
    simpa [lt_irrefl] using h
  expLocalHomeomorph.hasStrictDerivAt_symm h h0 <| by
    simpa [exp_log h0] using hasStrictDerivAt_exp (log x)
#align complex.has_strict_deriv_at_log Complex.hasStrictDerivAt_log

theorem hasStrictFderivAt_log_real {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictFderivAt log (x⁻¹ • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAt_log h).complexToReal_fderiv
#align complex.has_strict_fderiv_at_log_real Complex.hasStrictFderivAt_log_real

theorem contDiffAt_log {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) {n : ℕ∞} : ContDiffAt ℂ n log x :=
  expLocalHomeomorph.contDiffAt_symm_deriv (exp_ne_zero <| log x) h (hasDerivAt_exp _)
    contDiff_exp.contDiffAt
#align complex.cont_diff_at_log Complex.contDiffAt_log

end Complex

section LogDeriv

open Complex Filter

open Topology

variable {α : Type _} [TopologicalSpace α] {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictFderivAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} (h₁ : HasStrictFderivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictFderivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).comp_hasStrictFderivAt x h₁
#align has_strict_fderiv_at.clog HasStrictFderivAt.clog

theorem HasStrictDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x :=
  by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).comp x h₁
#align has_strict_deriv_at.clog HasStrictDerivAt.clog

theorem HasStrictDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using (hasStrictFderivAt_log_real h₂).comp_hasStrictDerivAt x h₁
#align has_strict_deriv_at.clog_real HasStrictDerivAt.clog_real

theorem HasFderivAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} (h₁ : HasFderivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasFderivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFderivAt x h₁
#align has_fderiv_at.clog HasFderivAt.clog

theorem HasDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivAt (fun t => log (f t)) (f' / f x) x :=
  by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp x h₁
#align has_deriv_at.clog HasDerivAt.clog

theorem HasDerivAt.clog_real {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using (hasStrictFderivAt_log_real h₂).hasFderivAt.comp_hasDerivAt x h₁
#align has_deriv_at.clog_real HasDerivAt.clog_real

theorem DifferentiableAt.clog {f : E → ℂ} {x : E} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableAt ℂ (fun t => log (f t)) x :=
  (h₁.hasFderivAt.clog h₂).differentiableAt
#align differentiable_at.clog DifferentiableAt.clog

theorem HasFderivWithinAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {s : Set E} {x : E}
    (h₁ : HasFderivWithinAt f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x :=
  (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasFderivWithinAt x h₁
#align has_fderiv_within_at.clog HasFderivWithinAt.clog

theorem HasDerivWithinAt.clog {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ} (h₁ : HasDerivWithinAt f f' s x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x :=
  by
  rw [div_eq_inv_mul]
  exact (hasStrictDerivAt_log h₂).hasDerivAt.comp_hasDerivWithinAt x h₁
#align has_deriv_within_at.clog HasDerivWithinAt.clog

theorem HasDerivWithinAt.clog_real {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} {f' : ℂ}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  simpa only [div_eq_inv_mul] using
    (hasStrictFderivAt_log_real h₂).hasFderivAt.comp_hasDerivWithinAt x h₁
#align has_deriv_within_at.clog_real HasDerivWithinAt.clog_real

theorem DifferentiableWithinAt.clog {f : E → ℂ} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt ℂ f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    DifferentiableWithinAt ℂ (fun t => log (f t)) s x :=
  (h₁.hasFderivWithinAt.clog h₂).differentiableWithinAt
#align differentiable_within_at.clog DifferentiableWithinAt.clog

theorem DifferentiableOn.clog {f : E → ℂ} {s : Set E} (h₁ : DifferentiableOn ℂ f s)
    (h₂ : ∀ x ∈ s, 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableOn ℂ (fun t => log (f t)) s :=
  fun x hx => (h₁ x hx).clog (h₂ x hx)
#align differentiable_on.clog DifferentiableOn.clog

theorem Differentiable.clog {f : E → ℂ} (h₁ : Differentiable ℂ f)
    (h₂ : ∀ x, 0 < (f x).re ∨ (f x).im ≠ 0) : Differentiable ℂ fun t => log (f t) := fun x =>
  (h₁ x).clog (h₂ x)
#align differentiable.clog Differentiable.clog

end LogDeriv

