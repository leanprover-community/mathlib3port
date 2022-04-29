/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/


open Filter Asymptotics

open TopologicalSpace

section NormedField

/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
theorem Filter.IsBoundedUnder.is_o_sub_self_inv {𝕜 E : Type _} [NormedField 𝕜] [HasNorm E] {a : 𝕜} {f : 𝕜 → E}
    (h : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (norm ∘ f)) : IsOₓ f (fun x => (x - a)⁻¹) (𝓝[≠] a) := by
  refine' (h.is_O_const (@one_ne_zero ℝ _ _)).trans_is_o (is_o_const_left.2 <| Or.inr _)
  simp only [(· ∘ ·), norm_inv]
  exact (tendsto_norm_sub_self_punctured_nhds a).inv_tendsto_zero

end NormedField

section LinearOrderedField

variable {𝕜 : Type _} [LinearOrderedField 𝕜]

theorem pow_div_pow_eventually_eq_at_top {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[at_top] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_gt_at_top (0 : 𝕜)).mono fun x hx => _
  simp [zpow_sub₀ hx.ne']

theorem pow_div_pow_eventually_eq_at_bot {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[at_bot] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_lt_at_bot (0 : 𝕜)).mono fun x hx => _
  simp [zpow_sub₀ hx.ne'.symm]

theorem tendsto_zpow_at_top_at_top {n : ℤ} (hn : 0 < n) : Tendsto (fun x : 𝕜 => x ^ n) atTop atTop := by
  lift n to ℕ using hn.le
  simp only [zpow_coe_nat]
  exact tendsto_pow_at_top (nat.succ_le_iff.mpr <| int.coe_nat_pos.mp hn)

theorem tendsto_pow_div_pow_at_top_at_top {p q : ℕ} (hpq : q < p) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop :=
  by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_at_top
  linarith

theorem tendsto_pow_div_pow_at_top_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_zero
  linarith

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜]

theorem Asymptotics.is_o_pow_pow_at_top_of_lt [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    IsOₓ (fun x : 𝕜 => x ^ p) (fun x => x ^ q) atTop := by
  refine' (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq)
  exact (eventually_gt_at_top 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsO.trans_tendsto_norm_at_top {α : Type _} {u v : α → 𝕜} {l : Filter α} (huv : IsO u v l)
    (hu : Tendsto (fun x => ∥u x∥) l atTop) : Tendsto (fun x => ∥v x∥) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [is_O_with] at hcuv
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
  ext x
  rw [mul_div_cancel_left _ hc.ne.symm]

end NormedLinearOrderedField

