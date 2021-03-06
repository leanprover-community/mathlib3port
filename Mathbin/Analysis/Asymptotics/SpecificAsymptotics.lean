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

/-- If `f : ๐ โ E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)โปยน)` as
`x โ a`, `x โ  a`. -/
theorem Filter.IsBoundedUnder.is_o_sub_self_inv {๐ E : Type _} [NormedField ๐] [HasNorm E] {a : ๐} {f : ๐ โ E}
    (h : IsBoundedUnder (ยท โค ยท) (๐[โ ] a) (norm โ f)) : f =o[๐[โ ] a] fun x => (x - a)โปยน := by
  refine' (h.is_O_const (@one_ne_zero โ _ _)).trans_is_o (is_o_const_left.2 <| Or.inr _)
  simp only [โ (ยท โ ยท), โ norm_inv]
  exact (tendsto_norm_sub_self_punctured_nhds a).inv_tendsto_zero

end NormedField

section LinearOrderedField

variable {๐ : Type _} [LinearOrderedField ๐]

theorem pow_div_pow_eventually_eq_at_top {p q : โ} :
    (fun x : ๐ => x ^ p / x ^ q) =แถ [at_top] fun x => x ^ ((p : โค) - q) := by
  apply (eventually_gt_at_top (0 : ๐)).mono fun x hx => _
  simp [โ zpow_subโ hx.ne']

theorem pow_div_pow_eventually_eq_at_bot {p q : โ} :
    (fun x : ๐ => x ^ p / x ^ q) =แถ [at_bot] fun x => x ^ ((p : โค) - q) := by
  apply (eventually_lt_at_bot (0 : ๐)).mono fun x hx => _
  simp [โ zpow_subโ hx.ne]

theorem tendsto_zpow_at_top_at_top {n : โค} (hn : 0 < n) : Tendsto (fun x : ๐ => x ^ n) atTop atTop := by
  lift n to โ using hn.le
  simp only [โ zpow_coe_nat]
  exact tendsto_pow_at_top (nat.cast_pos.mp hn).ne'

theorem tendsto_pow_div_pow_at_top_at_top {p q : โ} (hpq : q < p) : Tendsto (fun x : ๐ => x ^ p / x ^ q) atTop atTop :=
  by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_at_top
  linarith

theorem tendsto_pow_div_pow_at_top_zero [TopologicalSpace ๐] [OrderTopology ๐] {p q : โ} (hpq : p < q) :
    Tendsto (fun x : ๐ => x ^ p / x ^ q) atTop (๐ 0) := by
  rw [tendsto_congr' pow_div_pow_eventually_eq_at_top]
  apply tendsto_zpow_at_top_zero
  linarith

end LinearOrderedField

section NormedLinearOrderedField

variable {๐ : Type _} [NormedLinearOrderedField ๐]

theorem Asymptotics.is_o_pow_pow_at_top_of_lt [OrderTopology ๐] {p q : โ} (hpq : p < q) :
    (fun x : ๐ => x ^ p) =o[at_top] fun x => x ^ q := by
  refine' (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq)
  exact (eventually_gt_at_top 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim

theorem Asymptotics.IsO.trans_tendsto_norm_at_top {ฮฑ : Type _} {u v : ฮฑ โ ๐} {l : Filter ฮฑ} (huv : u =O[l] v)
    (hu : Tendsto (fun x => โฅu xโฅ) l atTop) : Tendsto (fun x => โฅv xโฅ) l atTop := by
  rcases huv.exists_pos with โจc, hc, hcuvโฉ
  rw [is_O_with] at hcuv
  convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
  ext x
  rw [mul_div_cancel_left _ hc.ne.symm]

end NormedLinearOrderedField

section Real

open BigOperators

open Finset

theorem Asymptotics.IsOโ.sum_range {ฮฑ : Type _} [NormedGroup ฮฑ] {f : โ โ ฮฑ} {g : โ โ โ} (h : f =o[at_top] g)
    (hg : 0 โค g) (h'g : Tendsto (fun n => โ i in range n, g i) atTop atTop) :
    (fun n => โ i in range n, f i) =o[at_top] fun n => โ i in range n, g i := by
  have A : โ i, โฅg iโฅ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : โ n, โฅโ i in range n, g iโฅ = โ i in range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply is_o_iff.2 fun ฮต ฮตpos => _
  obtain โจN, hNโฉ : โ N : โ, โ b : โ, N โค b โ โฅf bโฅ โค ฮต / 2 * g b := by
    simpa only [โ A, โ eventually_at_top] using is_o_iff.mp h (half_pos ฮตpos)
  have : (fun n : โ => โ i in range N, f i) =o[at_top] fun n : โ => โ i in range n, g i := by
    apply is_o_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [is_o_iff.1 this (half_pos ฮตpos), Ici_mem_at_top N] with n hn Nn
  calc โฅโ i in range n, f iโฅ = โฅ(โ i in range N, f i) + โ i in Ico N n, f iโฅ := by
      rw [sum_range_add_sum_Ico _ Nn]_ โค โฅโ i in range N, f iโฅ + โฅโ i in Ico N n, f iโฅ :=
      norm_add_le _ _ _ โค โฅโ i in range N, f iโฅ + โ i in Ico N n, ฮต / 2 * g i :=
      add_le_add le_rfl
        (norm_sum_le_of_le _ fun i hi =>
          hN _ (mem_Ico.1 hi).1)_ โค โฅโ i in range N, f iโฅ + โ i in range n, ฮต / 2 * g i :=
      by
      refine' add_le_add le_rfl _
      apply sum_le_sum_of_subset_of_nonneg
      ยท rw [range_eq_Ico]
        exact Ico_subset_Ico (zero_le _) le_rfl
        
      ยท intro i hi hident
        exact mul_nonneg (half_pos ฮตpos).le (hg i)
        _ โค ฮต / 2 * โฅโ i in range n, g iโฅ + ฮต / 2 * โ i in range n, g i :=
      by
      rw [โ mul_sum]
      exact add_le_add hn (mul_le_mul_of_nonneg_left le_rfl (half_pos ฮตpos).le)_ = ฮต * โฅโ i in range n, g iโฅ := by
      simp [โ B]
      ring

theorem Asymptotics.is_o_sum_range_of_tendsto_zero {ฮฑ : Type _} [NormedGroup ฮฑ] {f : โ โ ฮฑ}
    (h : Tendsto f atTop (๐ 0)) : (fun n => โ i in range n, f i) =o[at_top] fun n => (n : โ) := by
  have := ((is_o_one_iff โ).2 h).sum_range fun i => zero_le_one
  simp only [โ sum_const, โ card_range, โ Nat.smul_one_eq_coe] at this
  exact this tendsto_coe_nat_at_top_at_top

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type _} [NormedGroup E] [NormedSpace โ E] {u : โ โ E} {l : E}
    (h : Tendsto u atTop (๐ l)) : Tendsto (fun n : โ => (nโปยน : โ) โข โ i in range n, u i) atTop (๐ l) := by
  rw [โ tendsto_sub_nhds_zero_iff, โ is_o_one_iff โ]
  have := Asymptotics.is_o_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((is_O_refl (fun n : โ => (n : โ)โปยน) at_top).smul_is_o this).congr' _ _
  ยท filter_upwards [Ici_mem_at_top 1] with n npos
    have nposโ : (0 : โ) < n := Nat.cast_pos.2 npos
    simp only [โ smul_sub, โ sum_sub_distrib, โ sum_const, โ card_range, โ sub_right_inj]
    rw [nsmul_eq_smul_cast โ, smul_smul, inv_mul_cancel nposโ.ne', one_smul]
    
  ยท filter_upwards [Ici_mem_at_top 1] with n npos
    have nposโ : (0 : โ) < n := Nat.cast_pos.2 npos
    rw [Algebra.id.smul_eq_mul, inv_mul_cancel nposโ.ne']
    

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro {u : โ โ โ} {l : โ} (h : Tendsto u atTop (๐ l)) :
    Tendsto (fun n : โ => (nโปยน : โ) * โ i in range n, u i) atTop (๐ l) :=
  h.cesaro_smul

end Real

