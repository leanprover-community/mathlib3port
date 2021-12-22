import Mathbin.Analysis.NormedSpace.Ordered
import Mathbin.Analysis.Asymptotics.Asymptotics

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developped in `analysis.asymptotics.asymptotics`.
-/


open Filter Asymptotics

open_locale TopologicalSpace

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

theorem tendsto_zpow_at_top_at_top {n : ℤ} (hn : 0 < n) : tendsto (fun x : 𝕜 => x ^ n) at_top at_top := by
  lift n to ℕ using hn.le
  simp only [zpow_coe_nat]
  exact tendsto_pow_at_top (nat.succ_le_iff.mpr $ int.coe_nat_pos.mp hn)

theorem tendsto_pow_div_pow_at_top_at_top {p q : ℕ} (hpq : q < p) :
    tendsto (fun x : 𝕜 => x ^ p / x ^ q) at_top at_top := by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_at_top
  linarith

theorem tendsto_pow_div_pow_at_top_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    tendsto (fun x : 𝕜 => x ^ p / x ^ q) at_top (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_zero
  linarith

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type _} [NormedLinearOrderedField 𝕜]

theorem Asymptotics.is_o_pow_pow_at_top_of_lt [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    is_o (fun x : 𝕜 => x ^ p) (fun x => x ^ q) at_top := by
  refine' (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq)
  exact (eventually_gt_at_top 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsO.trans_tendsto_norm_at_top {α : Type _} {u v : α → 𝕜} {l : Filter α} (huv : is_O u v l)
    (hu : tendsto (fun x => ∥u x∥) l at_top) : tendsto (fun x => ∥v x∥) l at_top := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [is_O_with] at hcuv
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
  ext x
  rw [mul_div_cancel_left _ hc.ne.symm]

end NormedLinearOrderedField

