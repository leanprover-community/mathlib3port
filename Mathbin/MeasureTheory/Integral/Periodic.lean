/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.MeasureTheory.Group.FundamentalDomain
import Mathbin.MeasureTheory.Integral.IntervalIntegral

/-!
# Integrals of periodic functions

In this file we prove that `∫ x in b..b + a, f x = ∫ x in c..c + a, f x` for any (not necessarily
measurable) function periodic function with period `a`.
-/


open Set Function MeasureTheory MeasureTheory.Measure TopologicalSpace

open_locale MeasureTheory

theorem is_add_fundamental_domain_Ioc {a : ℝ} (ha : 0 < a) (b : ℝ)
    (μ : Measureₓ ℝ := by
      run_tac
        volume_tac) :
    IsAddFundamentalDomain (AddSubgroup.zmultiples a) (Ioc b (b + a)) μ := by
  refine' is_add_fundamental_domain.mk' measurable_set_Ioc fun x => _
  have : bijective (cod_restrict (fun n : ℤ => n • a) (AddSubgroup.zmultiples a) _) :=
    (Equivₓ.ofInjective (fun n : ℤ => n • a) (zsmul_strict_mono_left ha).Injective).Bijective
  refine' this.exists_unique_iff.2 _
  simpa only [add_commₓ x] using exists_unique_add_zsmul_mem_Ioc ha x b

variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [SecondCountableTopology E]

namespace Function

namespace Periodic

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
theorem interval_integral_add_eq_of_pos {f : ℝ → E} {a : ℝ} (hf : Periodic f a) (ha : 0 < a) (b c : ℝ) :
    (∫ x in b..b + a, f x) = ∫ x in c..c + a, f x := by
  have : Encodable (AddSubgroup.zmultiples a) := (countable_range _).toEncodable
  simp only [intervalIntegral.integral_of_le, ha.le, le_add_iff_nonneg_right]
  have : vadd_invariant_measure (AddSubgroup.zmultiples a) ℝ volume := ⟨fun c s hs => measure_preimage_add _ _ _⟩
  exact (is_add_fundamental_domain_Ioc ha b).set_integral_eq (is_add_fundamental_domain_Ioc ha c) hf.map_vadd_zmultiples

/-- If `f` is a periodic function with period `a`, then its integral over `[b, b + a]` does not
depend on `b`. -/
theorem interval_integral_add_eq {f : ℝ → E} {a : ℝ} (hf : Periodic f a) (b c : ℝ) :
    (∫ x in b..b + a, f x) = ∫ x in c..c + a, f x := by
  rcases lt_trichotomyₓ 0 a with (ha | rfl | ha)
  · exact hf.interval_integral_add_eq_of_pos ha b c
    
  · simp
    
  · rw [← neg_inj, ← intervalIntegral.integral_symm, ← intervalIntegral.integral_symm]
    simpa only [← sub_eq_add_neg, add_sub_cancel] using
      hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 ha) (b + a) (c + a)
    

end Periodic

end Function

