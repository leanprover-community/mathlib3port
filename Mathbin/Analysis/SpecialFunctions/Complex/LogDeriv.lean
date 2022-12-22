/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson

! This file was ported from Lean 3 source module analysis.special_functions.complex.log_deriv
! leanprover-community/mathlib commit 9116dd6709f303dcf781632e15fdef382b0fc579
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

open Real TopologicalSpace

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
        rw [mem_set_of_eq, ← of_real_def, exp_of_real_re]
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
    continuous_exp.ContinuousOn is_open_map_exp (is_open_Ioo.Preimage continuous_im)
#align complex.exp_local_homeomorph Complex.expLocalHomeomorph

theorem hasStrictDerivAtLog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) : HasStrictDerivAt log x⁻¹ x :=
  have h0 : x ≠ 0 := by 
    rintro rfl
    simpa [lt_irrefl] using h
  expLocalHomeomorph.hasStrictDerivAtSymm h h0 <| by
    simpa [exp_log h0] using has_strict_deriv_at_exp (log x)
#align complex.has_strict_deriv_at_log Complex.hasStrictDerivAtLog

theorem hasStrictFderivAtLogReal {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) :
    HasStrictFderivAt log (x⁻¹ • (1 : ℂ →L[ℝ] ℂ)) x :=
  (hasStrictDerivAtLog h).complexToRealFderiv
#align complex.has_strict_fderiv_at_log_real Complex.hasStrictFderivAtLogReal

theorem contDiffAtLog {x : ℂ} (h : 0 < x.re ∨ x.im ≠ 0) {n : ℕ∞} : ContDiffAt ℂ n log x :=
  expLocalHomeomorph.contDiffAtSymmDeriv (exp_ne_zero <| log x) h (hasDerivAtExp _)
    contDiffExp.ContDiffAt
#align complex.cont_diff_at_log Complex.contDiffAtLog

end Complex

section LogDeriv

open Complex Filter

open TopologicalSpace

variable {α : Type _} [TopologicalSpace α] {E : Type _} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem HasStrictFderivAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} (h₁ : HasStrictFderivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictFderivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAtLog h₂).compHasStrictFderivAt x h₁
#align has_strict_fderiv_at.clog HasStrictFderivAt.clog

theorem HasStrictDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (has_strict_deriv_at_log h₂).comp x h₁
#align has_strict_deriv_at.clog HasStrictDerivAt.clog

theorem HasStrictDerivAt.clogReal {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasStrictDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasStrictDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using (has_strict_fderiv_at_log_real h₂).compHasStrictDerivAt x h₁
#align has_strict_deriv_at.clog_real HasStrictDerivAt.clogReal

theorem HasFderivAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E} (h₁ : HasFderivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasFderivAt (fun t => log (f t)) ((f x)⁻¹ • f') x :=
  (hasStrictDerivAtLog h₂).HasDerivAt.compHasFderivAt x h₁
#align has_fderiv_at.clog HasFderivAt.clog

theorem HasDerivAt.clog {f : ℂ → ℂ} {f' x : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  rw [div_eq_inv_mul]
  exact (has_strict_deriv_at_log h₂).HasDerivAt.comp x h₁
#align has_deriv_at.clog HasDerivAt.clog

theorem HasDerivAt.clogReal {f : ℝ → ℂ} {x : ℝ} {f' : ℂ} (h₁ : HasDerivAt f f' x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivAt (fun t => log (f t)) (f' / f x) x := by
  simpa only [div_eq_inv_mul] using
    (has_strict_fderiv_at_log_real h₂).HasFderivAt.compHasDerivAt x h₁
#align has_deriv_at.clog_real HasDerivAt.clogReal

theorem DifferentiableAt.clog {f : E → ℂ} {x : E} (h₁ : DifferentiableAt ℂ f x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : DifferentiableAt ℂ (fun t => log (f t)) x :=
  (h₁.HasFderivAt.clog h₂).DifferentiableAt
#align differentiable_at.clog DifferentiableAt.clog

theorem HasFderivWithinAt.clog {f : E → ℂ} {f' : E →L[ℂ] ℂ} {s : Set E} {x : E}
    (h₁ : HasFderivWithinAt f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasFderivWithinAt (fun t => log (f t)) ((f x)⁻¹ • f') s x :=
  (hasStrictDerivAtLog h₂).HasDerivAt.compHasFderivWithinAt x h₁
#align has_fderiv_within_at.clog HasFderivWithinAt.clog

theorem HasDerivWithinAt.clog {f : ℂ → ℂ} {f' x : ℂ} {s : Set ℂ} (h₁ : HasDerivWithinAt f f' s x)
    (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) : HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  rw [div_eq_inv_mul]
  exact (has_strict_deriv_at_log h₂).HasDerivAt.compHasDerivWithinAt x h₁
#align has_deriv_within_at.clog HasDerivWithinAt.clog

theorem HasDerivWithinAt.clogReal {f : ℝ → ℂ} {s : Set ℝ} {x : ℝ} {f' : ℂ}
    (h₁ : HasDerivWithinAt f f' s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    HasDerivWithinAt (fun t => log (f t)) (f' / f x) s x := by
  simpa only [div_eq_inv_mul] using
    (has_strict_fderiv_at_log_real h₂).HasFderivAt.compHasDerivWithinAt x h₁
#align has_deriv_within_at.clog_real HasDerivWithinAt.clogReal

theorem DifferentiableWithinAt.clog {f : E → ℂ} {s : Set E} {x : E}
    (h₁ : DifferentiableWithinAt ℂ f s x) (h₂ : 0 < (f x).re ∨ (f x).im ≠ 0) :
    DifferentiableWithinAt ℂ (fun t => log (f t)) s x :=
  (h₁.HasFderivWithinAt.clog h₂).DifferentiableWithinAt
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

