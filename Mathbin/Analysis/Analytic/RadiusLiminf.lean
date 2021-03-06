/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Analysis.Analytic.Basic
import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Representation of `formal_multilinear_series.radius` as a `liminf`

In this file we prove that the radius of convergence of a `formal_multilinear_series` is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{β₯p nβ₯}}$. This lemma can't go to `basic.lean` because this
would create a circular dependency once we redefine `exp` using `formal_multilinear_series`.
-/


variable {π : Type _} [NondiscreteNormedField π] {E : Type _} [NormedGroup E] [NormedSpace π E] {F : Type _}
  [NormedGroup F] [NormedSpace π F]

open TopologicalSpace Classical BigOperators Nnreal Ennreal

open Filter Asymptotics

namespace FormalMultilinearSeries

variable (p : FormalMultilinearSeries π E F)

/-- The radius of a formal multilinear series is equal to
$\liminf_{n\to\infty} \frac{1}{\sqrt[n]{β₯p nβ₯}}$. The actual statement uses `ββ₯0` and some
coercions. -/
theorem radius_eq_liminf : p.radius = liminfβ atTop fun n => 1 / (β₯p nβ₯β ^ (1 / (n : β)) : ββ₯0 ) := by
  have : β (r : ββ₯0 ) {n : β}, 0 < n β ((r : ββ₯0β) β€ 1 / β(β₯p nβ₯β ^ (1 / (n : β))) β β₯p nβ₯β * r ^ n β€ 1) := by
    intro r n hn
    have : 0 < (n : β) := Nat.cast_pos.2 hn
    conv_lhs =>
      rw [one_div, Ennreal.le_inv_iff_mul_le, β Ennreal.coe_mul, Ennreal.coe_le_one_iff, one_div, β Nnreal.rpow_one r, β
        mul_inv_cancel this.ne', Nnreal.rpow_mul, β Nnreal.mul_rpow, β Nnreal.one_rpow nβ»ΒΉ,
        Nnreal.rpow_le_rpow_iff (inv_pos.2 this), mul_comm, Nnreal.rpow_nat_cast]
  apply le_antisymmβ <;> refine' Ennreal.le_of_forall_nnreal_lt fun r hr => _
  Β· rcases((tfae_exists_lt_is_o_pow (fun n => β₯p nβ₯ * r ^ n) 1).out 1 7).1 (p.is_o_of_lt_radius hr) with β¨a, ha, Hβ©
    refine'
      le_Liminf_of_le
        (by
          infer_auto_param)
        (eventually_map.2 <| _)
    refine' H.mp ((eventually_gt_at_top 0).mono fun n hnβ hn => (this _ hnβ).2 (Nnreal.coe_le_coe.1 _))
    push_cast
    exact (le_abs_self _).trans (hn.trans (pow_le_one _ ha.1.le ha.2.le))
    
  Β· refine' p.le_radius_of_is_O (is_O.of_bound 1 _)
    refine' (eventually_lt_of_lt_liminf hr).mp ((eventually_gt_at_top 0).mono fun n hnβ hn => _)
    simpa using Nnreal.coe_le_coe.2 ((this _ hnβ).1 hn.le)
    

end FormalMultilinearSeries

