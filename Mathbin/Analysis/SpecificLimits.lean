/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Johannes Hölzl, Yury G. Kudryashov,
         Dylan MacKenzie, Patrick Massot
-/
import Mathbin.Algebra.GeomSum
import Mathbin.Analysis.Asymptotics.Asymptotics
import Mathbin.Order.Filter.Archimedean
import Mathbin.Order.Iterate
import Mathbin.Topology.Instances.Ennreal

/-!
# A collection of specific limit computations
-/


noncomputable section

open Classical Set Function Filter Finset Metric Asymptotics

open_locale Classical TopologicalSpace Nat BigOperators uniformity Nnreal Ennreal

variable {α : Type _} {β : Type _} {ι : Type _}

theorem tendsto_norm_at_top_at_top : Tendsto (norm : ℝ → ℝ) atTop atTop :=
  tendsto_abs_at_top_at_top

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
    (∃ r, Tendsto (fun n => ∑ i in range n, abs (f i)) atTop (𝓝 r)) → Summable f
  | ⟨r, hr⟩ => by
    refine' summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩
    exact fun i => norm_nonneg _
    simpa only using hr

theorem tendsto_inverse_at_top_nhds_0_nat : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_at_top_zero.comp tendsto_coe_nat_at_top_at_top

theorem tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) := by
  simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

theorem Nnreal.tendsto_inverse_at_top_nhds_0_nat : Tendsto (fun n : ℕ => (n : ℝ≥0 )⁻¹) atTop (𝓝 0) := by
  rw [← Nnreal.tendsto_coe]
  convert tendsto_inverse_at_top_nhds_0_nat
  simp

theorem Nnreal.tendsto_const_div_at_top_nhds_0_nat (C : ℝ≥0 ) : Tendsto (fun n : ℕ => C / n) atTop (𝓝 0) := by
  simpa using tendsto_const_nhds.mul Nnreal.tendsto_inverse_at_top_nhds_0_nat

theorem tendsto_one_div_add_at_top_nhds_0_nat : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  suffices Tendsto (fun n : ℕ => 1 / (↑(n + 1) : ℝ)) atTop (𝓝 0) by
    simpa
  (tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/


theorem tendsto_add_one_pow_at_top_at_top_of_pos [LinearOrderedSemiring α] [Archimedean α] {r : α} (h : 0 < r) :
    Tendsto (fun n : ℕ => (r + 1) ^ n) atTop atTop :=
  (tendsto_at_top_at_top_of_monotone' fun n m => pow_le_pow (le_add_of_nonneg_left (le_of_ltₓ h))) <|
    not_bdd_above_iff.2 fun x => Set.exists_range_iff.2 <| add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_at_top_at_top_of_one_lt [LinearOrderedRing α] [Archimedean α] {r : α} (h : 1 < r) :
    Tendsto (fun n : ℕ => r ^ n) atTop atTop :=
  sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

theorem Nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) : Tendsto (fun n : ℕ => m ^ n) atTop atTop :=
  tsub_add_cancel_of_le (le_of_ltₓ h) ▸ tendsto_add_one_pow_at_top_at_top_of_pos (tsub_pos_of_lt h)

theorem tendsto_norm_zero' {𝕜 : Type _} [NormedGroup 𝕜] : Tendsto (norm : 𝕜 → ℝ) (𝓝[≠] 0) (𝓝[>] 0) :=
  tendsto_norm_zero.inf <| tendsto_principal_principal.2 fun x hx => norm_pos_iff.2 hx

namespace NormedField

theorem tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] :
    Tendsto (fun x : 𝕜 => ∥x⁻¹∥) (𝓝[≠] 0) atTop :=
  (tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr fun x => (norm_inv x).symm

theorem tendsto_norm_zpow_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] {m : ℤ} (hm : m < 0) :
    Tendsto (fun x : 𝕜 => ∥x ^ m∥) (𝓝[≠] 0) atTop := by
  rcases neg_surjective m with ⟨m, rfl⟩
  rw [neg_lt_zero] at hm
  lift m to ℕ using hm.le
  rw [Int.coe_nat_pos] at hm
  simp only [norm_pow, zpow_neg₀, zpow_coe_nat, ← inv_pow₀]
  exact (tendsto_pow_at_top hm).comp NormedField.tendsto_norm_inverse_nhds_within_0_at_top

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
theorem tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 𝔸 : Type _} [NormedField 𝕜] [NormedGroup 𝔸] [NormedSpace 𝕜 𝔸]
    {l : Filter ι} {ε : ι → 𝕜} {f : ι → 𝔸} (hε : Tendsto ε l (𝓝 0)) (hf : Filter.IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← is_o_one_iff 𝕜] at hε⊢
  simpa using is_o.smul_is_O hε (hf.is_O_const (one_ne_zero : (1 : 𝕜) ≠ 0))

@[simp]
theorem continuous_at_zpow {𝕜 : Type _} [NondiscreteNormedField 𝕜] {m : ℤ} {x : 𝕜} :
    ContinuousAt (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m := by
  refine' ⟨_, continuous_at_zpow₀ _ _⟩
  contrapose!
  rintro ⟨rfl, hm⟩ hc
  exact
    not_tendsto_at_top_of_tendsto_nhds (hc.tendsto.mono_left nhds_within_le_nhds).norm
      (tendsto_norm_zpow_nhds_within_0_at_top hm)

@[simp]
theorem continuous_at_inv {𝕜 : Type _} [NondiscreteNormedField 𝕜] {x : 𝕜} : ContinuousAt Inv.inv x ↔ x ≠ 0 := by
  simpa [(@zero_lt_one ℤ _ _).not_le] using @continuous_at_zpow _ _ (-1) x

end NormedField

theorem tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
    [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun this : 0 = r =>
      (tendsto_add_at_top_iff_nat 1).mp <| by
        simp [pow_succₓ, ← this, tendsto_const_nhds])
    fun this : 0 < r =>
    have : Tendsto (fun n => (r⁻¹ ^ n)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt <| one_lt_inv this h₂)
    this.congr fun n => by
      simp

theorem tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜]
    [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
    Tendsto (fun n : ℕ => r ^ n) atTop (𝓝[>] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_at_top_nhds_0_of_lt_1 h₁.le h₂, tendsto_principal.2 <| eventually_of_forall fun n => pow_pos h₁ _⟩

theorem is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    IsOₓ (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) atTop :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (is_o_of_tendsto fun n hn => False.elim <| H.ne' <| pow_eq_zero hn) <|
    (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun n =>
      div_pow _ _ _

theorem is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    IsO (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) atTop :=
  h₂.eq_or_lt.elim (fun h => h ▸ is_O_refl _ _) fun h => (is_o_pow_pow_of_lt_left h₁ h).IsO

theorem is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : abs r₁ < abs r₂) :
    IsOₓ (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) atTop := by
  refine' (is_o.of_norm_left _).of_norm_right
  exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
     for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
theorem tfae_exists_lt_is_o_pow (f : ℕ → ℝ) (R : ℝ) :
    Tfae
      [∃ a ∈ ioo (-R) R, IsOₓ f (pow a) atTop, ∃ a ∈ ioo 0 R, IsOₓ f (pow a) atTop,
        ∃ a ∈ ioo (-R) R, IsO f (pow a) atTop, ∃ a ∈ ioo 0 R, IsO f (pow a) atTop,
        ∃ a < R, ∃ (C : _)(h₀ : 0 < C ∨ 0 < R), ∀ n, abs (f n) ≤ C * a ^ n,
        ∃ a ∈ ioo 0 R, ∃ C > 0, ∀ n, abs (f n) ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n,
        ∃ a ∈ ioo 0 R, ∀ᶠ n in at_top, abs (f n) ≤ a ^ n] :=
  by
  have A : Ico 0 R ⊆ Ioo (-R) R := fun x hx => ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsO⟩
  tfae_have 2 → 1
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  tfae_have 3 → 2
  · rintro ⟨a, ha, H⟩
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact
      ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩, H.trans_is_o (is_o_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
    
  tfae_have 2 → 4
  exact fun ⟨a, ha, H⟩ => ⟨a, ha, H.IsO⟩
  tfae_have 4 → 3
  exact fun ⟨a, ha, H⟩ => ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  · rintro ⟨a, ha, H⟩
    rcases bound_of_is_O_nat_at_top H with ⟨C, hC₀, hC⟩
    refine' ⟨a, ha, C, hC₀, fun n => _⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
    
  tfae_have 6 → 5
  exact fun ⟨a, ha, C, H₀, H⟩ => ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  · rintro ⟨a, ha, C, h₀, H⟩
    rcases sign_cases_of_C_mul_pow_nonneg fun n => (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irreflₓ, false_orₓ] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩
      
    exact ⟨a, A ⟨ha₀, ha⟩, is_O_of_le' _ fun n => (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
    
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  · rintro ⟨a, ha, H⟩
    refine' ⟨a, ha, (H.def zero_lt_one).mono fun n hn => _⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mulₓ, abs_pow, abs_of_pos ha.1] at hn
    
  tfae_have 8 → 7
  exact fun ⟨a, ha, H⟩ => ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  · rintro ⟨a, ha, H⟩
    have : 0 ≤ a := nonneg_of_eventually_pow_nonneg (H.mono fun n => (abs_nonneg _).trans)
    refine' ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩
    simpa only [Real.norm_eq_abs, one_mulₓ, abs_pow, abs_of_nonneg this]
    
  tfae_finish

theorem uniformity_basis_dist_pow_of_lt_1 {α : Type _} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
    (𝓤 α).HasBasis (fun k : ℕ => True) fun k => { p : α × α | dist p.1 p.2 < r ^ k } :=
  (Metric.mk_uniformity_basis fun i _ => pow_pos h₀ _) fun ε ε0 =>
    (exists_pow_lt_of_lt_one ε0 h₁).imp fun k hk => ⟨trivialₓ, hk.le⟩

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀, ∀ k < n, ∀, c * u k < u (k + 1)) :
    c ^ n * u 0 < u n := by
  refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
  · simp
    
  · simp [pow_succₓ, mul_assoc, le_reflₓ]
    

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀, ∀ k < n, ∀, c * u k ≤ u (k + 1)) : c ^ n * u 0 ≤ u n :=
  by
  refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;> simp [pow_succₓ, mul_assoc, le_reflₓ]

theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀, ∀ k < n, ∀, u (k + 1) < c * u k) :
    u n < c ^ n * u 0 := by
  refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
  · simp
    
  · simp [pow_succₓ, mul_assoc, le_reflₓ]
    

theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀, ∀ k < n, ∀, u (k + 1) ≤ c * u k) : u n ≤ c ^ n * u 0 :=
  by
  refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;> simp [pow_succₓ, mul_assoc, le_reflₓ]

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_const_pow_of_one_lt {R : Type _} [NormedRing R] (k : ℕ) {r : ℝ} (hr : 1 < r) :
    IsOₓ (fun n => n ^ k : ℕ → R) (fun n => r ^ n) atTop := by
  have : tendsto (fun x : ℝ => x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ := ((this.eventually (gt_mem_nhds hr)).And self_mem_nhds_within).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices : is_O _ (fun n : ℕ => (r' ^ k) ^ n) at_top
  exact this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mulₓ, mul_comm, pow_mulₓ]
  suffices : ∀ n : ℕ, ∥(n : R)∥ ≤ (r' - 1)⁻¹ * ∥(1 : R)∥ * ∥r' ^ n∥
  exact (is_O_of_le' _ this).pow _
  intro n
  rw [mul_right_commₓ]
  refine' n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
  simpa [div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem is_o_coe_const_pow_of_one_lt {R : Type _} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    IsOₓ (coe : ℕ → R) (fun n => r ^ n) atTop := by
  simpa only [pow_oneₓ] using is_o_pow_const_const_pow_of_one_lt 1 hr

/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type _} [NormedRing R] (k : ℕ) {r₁ : R} {r₂ : ℝ}
    (h : ∥r₁∥ < r₂) : IsOₓ (fun n => n ^ k * r₁ ^ n : ℕ → R) (fun n => r₂ ^ n) atTop := by
  by_cases' h0 : r₁ = 0
  · refine' (is_o_zero _ _).congr' (mem_at_top_sets.2 <| ⟨1, fun n hn => _⟩) eventually_eq.rfl
    simp [zero_pow (zero_lt_one.trans_le hn), h0]
    
  rw [← Ne.def, ← norm_pos_iff] at h0
  have A : is_o (fun n => n ^ k : ℕ → R) (fun n => (r₂ / ∥r₁∥) ^ n) at_top :=
    is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices is_O (fun n => r₁ ^ n) (fun n => ∥r₁∥ ^ n) at_top by
    simpa [div_mul_cancel _ (pow_pos h0 _).ne'] using A.mul_is_O this
  exact
    is_O.of_bound 1
      (by
        simpa using eventually_norm_pow_le r₁)

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n => n ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (is_o_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : abs r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases' h0 : r = 0
  · exact
      tendsto_const_nhds.congr'
        (mem_at_top_sets.2
          ⟨1, fun n hn => by
            simp [zero_lt_one.trans_le hn, h0]⟩)
    
  have hr' : 1 < (abs r)⁻¹ := one_lt_inv (abs_pos.2 h0) hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : abs r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_oneₓ] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n => n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_oneₓ] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c) (hu : ∀ n, c * v n ≤ v (n + 1)) :
    Tendsto v atTop atTop :=
  (tendsto_at_top_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k hk => hu k) <|
    (tendsto_pow_at_top_at_top_of_one_lt hc).at_top_mul_const h₀

theorem Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0 } (hr : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  Nnreal.tendsto_coe.1 <| by
    simp only [Nnreal.coe_pow, Nnreal.coe_zero, tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

theorem Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0∞} (hr : r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  by
  rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
  rw [← Ennreal.coe_zero]
  norm_cast  at *
  apply Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
theorem tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type _} [NormedRing R] {x : R} (h : ∥x∥ < 1) :
    Tendsto (fun n : ℕ => x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h

theorem tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : Tendsto (fun n : ℕ => r ^ n) atTop (𝓝 0) :=
  tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/


section Geometric

theorem has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  have : r ≠ 1 := ne_of_ltₓ h₂
  have : Tendsto (fun n => (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds
  have : (fun n => ∑ i in range n, r ^ i) = fun n => geomSum r n := rfl
  (has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr <| by
    simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]

theorem summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

theorem tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (has_sum_geometric_of_lt_1 h₁ h₂).tsum_eq

theorem has_sum_geometric_two : HasSum (fun n : ℕ => ((1 : ℝ) / 2) ^ n) 2 := by
  convert has_sum_geometric_of_lt_1 _ _ <;> norm_num

theorem summable_geometric_two : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
  ⟨_, has_sum_geometric_two⟩

theorem summable_geometric_two_encode {ι : Type _} [Encodable ι] :
    Summable fun i : ι => (1 / 2 : ℝ) ^ Encodable.encode i :=
  summable_geometric_two.comp_injective Encodable.encode_injective

theorem tsum_geometric_two : (∑' n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  has_sum_geometric_two.tsum_eq

theorem sum_geometric_two_le (n : ℕ) : (∑ i : ℕ in range n, (1 / (2 : ℝ)) ^ i) ≤ 2 := by
  have : ∀ i, 0 ≤ (1 / (2 : ℝ)) ^ i := by
    intro i
    apply pow_nonneg
    norm_num
  convert sum_le_tsum (range n) (fun i _ => this i) summable_geometric_two
  exact tsum_geometric_two.symm

theorem tsum_geometric_inv_two : (∑' n : ℕ, (2 : ℝ)⁻¹ ^ n) = 2 :=
  (inv_eq_one_div (2 : ℝ)).symm ▸ tsum_geometric_two

/-- The sum of `2⁻¹ ^ i` for `n ≤ i` equals `2 * 2⁻¹ ^ n`. -/
theorem tsum_geometric_inv_two_ge (n : ℕ) : (∑' i, ite (n ≤ i) ((2 : ℝ)⁻¹ ^ i) 0) = 2 * 2⁻¹ ^ n := by
  have A : Summable fun i : ℕ => ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0 := by
    apply summable_of_nonneg_of_le _ _ summable_geometric_two <;>
      · intro i
        by_cases' hi : n ≤ i <;> simp [hi]
        
  have B : ((Finset.range n).Sum fun i : ℕ => ite (n ≤ i) ((2⁻¹ : ℝ) ^ i) 0) = 0 :=
    Finset.sum_eq_zero fun i hi => ite_eq_right_iff.2 fun h => (lt_irreflₓ _ ((Finset.mem_range.1 hi).trans_le h)).elim
  simp only [← sum_add_tsum_nat_add n A, B, if_true, zero_addₓ, zero_le', le_add_iff_nonneg_left, pow_addₓ,
    tsum_mul_right, tsum_geometric_inv_two]

theorem has_sum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ => a / 2 / 2 ^ n) a := by
  convert HasSum.mul_left (a / 2) (has_sum_geometric_of_lt_1 (le_of_ltₓ one_half_pos) one_half_lt_one)
  · funext n
    simp
    rfl
    
  · norm_num
    

theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ => a / 2 / 2 ^ n :=
  ⟨a, has_sum_geometric_two' a⟩

theorem tsum_geometric_two' (a : ℝ) : (∑' n : ℕ, a / 2 / 2 ^ n) = a :=
  (has_sum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
theorem Nnreal.has_sum_geometric {r : ℝ≥0 } (hr : r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ := by
  apply Nnreal.has_sum_coe.1
  push_cast
  rw [Nnreal.coe_sub (le_of_ltₓ hr)]
  exact has_sum_geometric_of_lt_1 r.coe_nonneg hr

theorem Nnreal.summable_geometric {r : ℝ≥0 } (hr : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, Nnreal.has_sum_geometric hr⟩

theorem tsum_geometric_nnreal {r : ℝ≥0 } (hr : r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (Nnreal.has_sum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
theorem Ennreal.tsum_geometric (r : ℝ≥0∞) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ := by
  cases' lt_or_leₓ r 1 with hr hr
  · rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    norm_cast  at *
    convert Ennreal.tsum_coe_eq (Nnreal.has_sum_geometric hr)
    rw [Ennreal.coe_inv <| ne_of_gtₓ <| tsub_pos_iff_lt.2 hr]
    
  · rw [tsub_eq_zero_iff_le.mpr hr, Ennreal.inv_zero, Ennreal.tsum_eq_supr_nat, supr_eq_top]
    refine' fun a ha => (Ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn => lt_of_lt_of_leₓ hn _
    calc (n : ℝ≥0∞) = ∑ i in range n, 1 := by
        rw [sum_const, nsmul_one, card_range]_ ≤ ∑ i in range n, r ^ i :=
        sum_le_sum fun k _ => one_le_pow_of_one_le' hr k
    

variable {K : Type _} [NormedField K] {ξ : K}

theorem has_sum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : HasSum (fun n : ℕ => ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : tendsto (fun n => (ξ ^ n - 1) * (ξ - 1)⁻¹) at_top (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds
  have B : (fun n => ∑ i in range n, ξ ^ i) = fun n => geomSum ξ n := rfl
  rw [has_sum_iff_tendsto_nat_of_summable_norm, B]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
    
  · simp [norm_pow, summable_geometric_of_lt_1 (norm_nonneg _) h]
    

theorem summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : Summable fun n : ℕ => ξ ^ n :=
  ⟨_, has_sum_geometric_of_norm_lt_1 h⟩

theorem tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : (∑' n : ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
  (has_sum_geometric_of_norm_lt_1 h).tsum_eq

theorem has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : HasSum (fun n : ℕ => r ^ n) (1 - r)⁻¹ :=
  has_sum_geometric_of_norm_lt_1 h

theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : Summable fun n : ℕ => r ^ n :=
  summable_geometric_of_norm_lt_1 h

theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : abs r < 1) : (∑' n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_1 : (Summable fun n : ℕ => ξ ^ n) ↔ ∥ξ∥ < 1 := by
  refine' ⟨fun h => _, summable_geometric_of_norm_lt_1⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ := (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow _ zero_le_one hk

end Geometric

section MulGeometric

theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] (k : ℕ) {r : R} (hr : ∥r∥ < 1) :
    Summable fun n : ℕ => ∥(n ^ k * r ^ n : R)∥ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  exact
    summable_of_is_O_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
      (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').IsO.norm_left

theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] [CompleteSpace R] (k : ℕ) {r : R}
    (hr : ∥r∥ < 1) : Summable (fun n => n ^ k * r ^ n : ℕ → R) :=
  summable_of_summable_norm <| summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem has_sum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    HasSum (fun n => n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  have A : Summable (fun n => n * r ^ n : ℕ → 𝕜) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_1 1 hr
  have B : HasSum (pow r : ℕ → 𝕜) (1 - r)⁻¹ := has_sum_geometric_of_norm_lt_1 hr
  refine' A.has_sum_iff.2 _
  have hr' : r ≠ 1 := by
    rintro rfl
    simpa [lt_irreflₓ] using hr
  set s : 𝕜 := ∑' n : ℕ, n * r ^ n
  calc s = (1 - r) * s / (1 - r) := (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm _ = (s - r * s) / (1 - r) :=
      by
      rw [sub_mul, one_mulₓ]_ = (((0 : ℕ) * r ^ 0 + ∑' n : ℕ, (n + 1) * r ^ (n + 1)) - r * s) / (1 - r) := by
      congr
      exact tsum_eq_zero_add A _ = ((r * ∑' n : ℕ, (n + 1) * r ^ n) - r * s) / (1 - r) := by
      simp [pow_succₓ, mul_left_commₓ _ r, tsum_mul_left]_ = r / (1 - r) ^ 2 := by
      simp [add_mulₓ, tsum_add A B.summable, mul_addₓ, B.tsum_eq, ← div_eq_mul_inv, sq, div_div_eq_div_mul]

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
    (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (has_sum_coe_mul_geometric_of_norm_lt_1 hr).tsum_eq

end MulGeometric

/-!
### Sequences with geometrically decaying distance in metric spaces

In this paragraph, we discuss sequences in metric spaces or emetric spaces for which the distance
between two consecutive terms decays geometrically. We show that such sequences are Cauchy
sequences, and bound their distances to the limit. We also discuss series with geometrically
decaying terms.
-/


section EdistLeGeometric

variable [PseudoEmetricSpace α] (r C : ℝ≥0∞) (hr : r < 1) (hC : C ≠ ⊤) {f : ℕ → α}
  (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric : CauchySeq f := by
  refine' cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _
  rw [Ennreal.tsum_mul_left, Ennreal.tsum_geometric]
  refine' Ennreal.mul_ne_top hC (Ennreal.inv_ne_top.2 _)
  exact (tsub_pos_iff_lt.2 hr).ne'

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    edist (f n) a ≤ C * r ^ n / (1 - r) := by
  convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _
  simp only [pow_addₓ, Ennreal.tsum_mul_left, Ennreal.tsum_geometric, div_eq_mul_inv, mul_assoc]

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : edist (f 0) a ≤ C / (1 - r) :=
  by
  simpa only [pow_zeroₓ, mul_oneₓ] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EdistLeGeometric

section EdistLeGeometricTwo

variable [PseudoEmetricSpace α] (C : ℝ≥0∞) (hC : C ≠ ⊤) {f : ℕ → α} (hu : ∀ n, edist (f n) (f (n + 1)) ≤ C / 2 ^ n)
  {a : α} (ha : Tendsto f atTop (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric_two : CauchySeq f := by
  simp only [div_eq_mul_inv, Ennreal.inv_pow] at hu
  refine' cauchy_seq_of_edist_le_geometric 2⁻¹ C _ hC hu
  simp [Ennreal.one_lt_two]

omit hC

include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) : edist (f n) a ≤ 2 * C / 2 ^ n := by
  simp only [div_eq_mul_inv, Ennreal.inv_pow] at *
  rw [mul_assoc, mul_comm]
  convert edist_le_of_edist_le_geometric_of_tendsto 2⁻¹ C hu ha n
  rw [Ennreal.one_sub_inv_two, inv_invₓ]

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2 * C := by
  simpa only [pow_zeroₓ, div_eq_mul_inv, Ennreal.inv_one, mul_oneₓ] using
    edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EdistLeGeometricTwo

section LeGeometric

variable [PseudoMetricSpace α] {r C : ℝ} (hr : r < 1) {f : ℕ → α} (hu : ∀ n, dist (f n) (f (n + 1)) ≤ C * r ^ n)

include hr hu

theorem aux_has_sum_of_le_geometric : HasSum (fun n : ℕ => C * r ^ n) (C / (1 - r)) := by
  rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨C₀, r₀⟩)
  · simp [has_sum_zero]
    
  · refine' HasSum.mul_left C _
    simpa using has_sum_geometric_of_lt_1 r₀ hr
    

variable (r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchy_seq_of_le_geometric : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ C / (1 - r) :=
  (aux_has_sum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C * r ^ n / (1 - r) := by
  have := aux_has_sum_of_le_geometric hr hu
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n
  simp only [pow_addₓ, mul_left_commₓ C, mul_div_right_comm]
  rw [mul_comm]
  exact (this.mul_left _).tsum_eq.symm

omit hr hu

variable (hu₂ : ∀ n, dist (f n) (f (n + 1)) ≤ C / 2 / 2 ^ n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchy_seq_of_le_geometric_two : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu₂ <| ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : Tendsto f atTop (𝓝 a)) : dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : Tendsto f atTop (𝓝 a)) (n : ℕ) :
    dist (f n) a ≤ C / 2 ^ n := by
  convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n
  simp only [add_commₓ n, pow_addₓ, ← div_div_eq_div_mul]
  symm
  exact ((has_sum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

section SummableLeGeometric

variable [SemiNormedGroup α] {r C : ℝ} {f : ℕ → α}

theorem SemiNormedGroup.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1) {u : ℕ → α}
    (h : ∀ n, ∥u n - u (n + 1)∥ ≤ C * r ^ n) : CauchySeq u :=
  cauchy_seq_of_le_geometric r C hr
    (by
      simpa [dist_eq_norm] using h)

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel']
  exact hf n

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ => ∑ x in s, f x :=
  cauchy_seq_finset_of_norm_bounded _ (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).Summable
    hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C * r ^ n) {a : α} (ha : HasSum f a)
    (n : ℕ) : ∥(∑ x in Finset.range n, f x) - a∥ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) : dist (∑ k in range (n + 1), u k) (∑ k in range n, u k) = ∥u n∥ := by
  simp [dist_eq_norm, sum_range_succ]

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) : dist (∑ k in range n, u k) (∑ k in range (n + 1), u k) = ∥u n∥ := by
  simp [dist_eq_norm', sum_range_succ]

theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1) (h : ∀ n, ∥u n∥ ≤ C * r ^ n) :
    CauchySeq fun n => ∑ k in range n, u k :=
  cauchy_seq_of_le_geometric r C hr
    (by
      simp [h])

theorem NormedGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_at_top_nat 1

theorem NormedGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1)
    (h : ∀, ∀ n ≥ N, ∀, ∥u n∥ ≤ C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k := by
  set v : ℕ → α := fun n => if n < N then 0 else u n
  have hC : 0 ≤ C := (zero_le_mul_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_reflₓ N)
  have : ∀, ∀ n ≥ N, ∀, u n = v n := by
    intro n hn
    simp [v, hn, if_neg (not_lt.mpr hn)]
  refine' cauchy_seq_sum_of_eventually_eq this (NormedGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
    
  intro n
  dsimp [v]
  split_ifs with H H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
    
  · push_neg  at H
    exact h _ H
    

end SummableLeGeometric

section NormedRingGeometric

variable {R : Type _} [NormedRing R] [CompleteSpace R]

open NormedSpace

/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem NormedRing.summable_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) : Summable fun n : ℕ => x ^ n := by
  have h1 : Summable fun n : ℕ => ∥x∥ ^ n := summable_geometric_of_lt_1 (norm_nonneg _) h
  refine' summable_of_norm_bounded_eventually _ h1 _
  rw [Nat.cofinite_eq_at_top]
  exact eventually_norm_pow_le x

/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
theorem NormedRing.tsum_geometric_of_norm_lt_1 (x : R) (h : ∥x∥ < 1) :
    ∥∑' n : ℕ, x ^ n∥ ≤ ∥(1 : R)∥ - 1 + (1 - ∥x∥)⁻¹ := by
  rw [tsum_eq_zero_add (NormedRing.summable_geometric_of_norm_lt_1 x h)]
  simp only [pow_zeroₓ]
  refine' le_transₓ (norm_add_le _ _) _
  have : ∥∑' b : ℕ, (fun n => x ^ (n + 1)) b∥ ≤ (1 - ∥x∥)⁻¹ - 1 := by
    refine' tsum_of_norm_bounded _ fun b => norm_pow_le' _ (Nat.succ_posₓ b)
    convert (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h)
    simp
  linarith

theorem geom_series_mul_neg (x : R) (h : ∥x∥ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_right (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← geom_sum_mul_neg, geom_sum_def, Finset.sum_mul]

theorem mul_neg_geom_series (x : R) (h : ∥x∥ < 1) : ((1 - x) * ∑' i : ℕ, x ^ i) = 1 := by
  have := (NormedRing.summable_geometric_of_norm_lt_1 x h).HasSum.mul_left (1 - x)
  refine' tendsto_nhds_unique this.tendsto_sum_nat _
  have : tendsto (fun n : ℕ => 1 - x ^ n) at_top (nhds 1) := by
    simpa using tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)
  convert ← this
  ext n
  rw [← mul_neg_geom_sum, geom_sum_def, Finset.mul_sum]

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/


theorem summable_of_ratio_norm_eventually_le {α : Type _} [SemiNormedGroup α] [CompleteSpace α] {f : ℕ → α} {r : ℝ}
    (hr₁ : r < 1) (h : ∀ᶠ n in at_top, ∥f (n + 1)∥ ≤ r * ∥f n∥) : Summable f := by
  by_cases' hr₀ : 0 ≤ r
  · rw [eventually_at_top] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine'
      summable_of_norm_bounded (fun n => ∥f N∥ * r ^ n) (Summable.mul_left _ <| summable_geometric_of_lt_1 hr₀ hr₁)
        fun n => _
    conv_rhs => rw [mul_comm, ← zero_addₓ N]
    refine' le_geom hr₀ n fun i _ => _
    convert hN (i + N) (N.le_add_left i) using 3
    ac_rfl
    
  · push_neg  at hr₀
    refine' summable_of_norm_bounded_eventually 0 summable_zero _
    rw [Nat.cofinite_eq_at_top]
    filter_upwards [h] with _ hn
    by_contra' h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_ltₓ hn <| mul_neg_of_neg_of_pos hr₀ h)
    

theorem summable_of_ratio_test_tendsto_lt_one {α : Type _} [NormedGroup α] [CompleteSpace α] {f : ℕ → α} {l : ℝ}
    (hl₁ : l < 1) (hf : ∀ᶠ n in at_top, f n ≠ 0) (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) :
    Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine' summable_of_ratio_norm_eventually_le hr₁ _
  filter_upwards [eventually_le_of_tendsto_lt hr₀ h, hf] with _ _ h₁
  rwa [← div_le_iff (norm_pos_iff.mpr h₁)]

theorem not_summable_of_ratio_norm_eventually_ge {α : Type _} [SemiNormedGroup α] {f : ℕ → α} {r : ℝ} (hr : 1 < r)
    (hf : ∃ᶠ n in at_top, ∥f n∥ ≠ 0) (h : ∀ᶠ n in at_top, r * ∥f n∥ ≤ ∥f (n + 1)∥) : ¬Summable f := by
  rw [eventually_at_top] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_at_top] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine' mt Summable.tendsto_at_top_zero fun h' => not_tendsto_at_top_of_tendsto_nhds (tendsto_norm_zero.comp h') _
  convert tendsto_at_top_of_geom_le _ hr _
  · refine' lt_of_le_of_neₓ (norm_nonneg _) _
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_app, zero_addₓ] at h''
    exact hN h''.symm
    
  · intro i
    dsimp only [comp_app]
    convert hN₀ (i + N) (hNN₀.trans (N.le_add_left i)) using 3
    ac_rfl
    

theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type _} [SemiNormedGroup α] {f : ℕ → α} {l : ℝ} (hl : 1 < l)
    (h : Tendsto (fun n => ∥f (n + 1)∥ / ∥f n∥) atTop (𝓝 l)) : ¬Summable f := by
  have key : ∀ᶠ n in at_top, ∥f n∥ ≠ 0 := by
    filter_upwards [eventually_ge_of_tendsto_gt hl h] with _ hn hc
    rw [hc, div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine' not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _
  filter_upwards [eventually_ge_of_tendsto_gt hr₁ h, key] with _ _ h₁
  rwa [← le_div_iff (lt_of_le_of_neₓ (norm_nonneg _) h₁.symm)]

/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
    Summable fun i => 1 / m ^ f i := by
  refine'
    summable_of_nonneg_of_le (fun a => one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (fun a => _)
      (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
        ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
  rw [div_pow, one_pow]
  refine' (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a)) <;> exact pow_pos (zero_lt_one.trans hm) _

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type _} [NormedGroup E] [NormedSpace ℝ E]

variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's Test** for monotone sequences. -/
theorem Monotone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hgb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ_posₓ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub, tsub_zero]
  apply
    (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
          ⟨b, eventually_map.mpr <| eventually_of_forall fun n => hgb <| n + 1⟩).CauchySeq.add
  apply (cauchy_seq_range_of_norm_bounded _ _ (_ : ∀ n, _ ≤ b * abs (f (n + 1) - f n))).neg
  · exact normed_uniform_group
    
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succₓ _))), ← mul_sum]
    apply real.uniform_continuous_mul_const.comp_cauchy_seq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (tendsto.cauchy_seq hf0).AddConst
    
  · intro n
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)
    

/-- **Dirichlet's test** for antitone sequences. -/
theorem Antitone.cauchy_seq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0))
    (hzb : ∀ n, ∥∑ i in range n, z i∥ ≤ b) : CauchySeq fun n => ∑ i in range (n + 1), f i • z i := by
  have hfa' : Monotone fun n => -f n := fun _ _ hab => neg_le_neg <| hfa hab
  have hf0' : tendsto (fun n => -f n) at_top (𝓝 0) := by
    convert hf0.neg
    norm_num
  convert (hfa'.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  funext
  simp

theorem norm_sum_neg_one_pow_le (n : ℕ) : ∥∑ i in range n, (-1 : ℝ) ^ i∥ ≤ 1 := by
  rw [← geom_sum_def, neg_one_geom_sum]
  split_ifs <;> norm_num

/-- The **alternating series test** for monotone sequences.
See also `tendsto_alternating_series_of_monotone_tendsto_zero`. -/
theorem Monotone.cauchy_seq_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), -1 ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences. -/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), -1 ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete <| hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

/-- The **alternating series test** for antitone sequences.
See also `tendsto_alternating_series_of_antitone_tendsto_zero`. -/
theorem Antitone.cauchy_seq_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    CauchySeq fun n => ∑ i in range (n + 1), -1 ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchy_seq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n => ∑ i in range (n + 1), -1 ^ i * f i) atTop (𝓝 l) :=
  cauchy_seq_tendsto_of_complete <| hfa.cauchy_seq_alternating_series_of_tendsto_zero hf0

end

/-! ### Positive sequences with small sums on encodable types -/


/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def posSumOfEncodable {ε : ℝ} (hε : 0 < ε) ι [Encodable ι] :
    { ε' : ι → ℝ // (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c ≤ ε } := by
  let f := fun n => ε / 2 / 2 ^ n
  have hf : HasSum f ε := has_sum_geometric_two' _
  have f0 : ∀ n, 0 < f n := fun n => div_pos (half_pos hε) (pow_pos zero_lt_two _)
  refine' ⟨f ∘ Encodable.encode, fun i => f0 _, _⟩
  rcases hf.summable.comp_injective (@Encodable.encode_injective ι _) with ⟨c, hg⟩
  refine' ⟨c, hg, has_sum_le_inj _ (@Encodable.encode_injective ι _) _ _ hg hf⟩
  · intro i _
    exact le_of_ltₓ (f0 _)
    
  · intro n
    exact le_rfl
    

theorem Set.Countable.exists_pos_has_sum_le {ι : Type _} {s : Set ι} (hs : s.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∃ c, HasSum (fun i : s => ε' i) c ∧ c ≤ ε := by
  have := hs.to_encodable
  rcases posSumOfEncodable hε s with ⟨f, hf0, ⟨c, hfc, hcε⟩⟩
  refine' ⟨fun i => if h : i ∈ s then f ⟨i, h⟩ else 1, fun i => _, ⟨c, _, hcε⟩⟩
  · split_ifs
    exacts[hf0 _, zero_lt_one]
    
  · simpa only [Subtype.coe_prop, dif_pos, Subtype.coe_eta]
    

theorem Set.Countable.exists_pos_forall_sum_le {ι : Type _} {s : Set ι} (hs : s.Countable) {ε : ℝ} (hε : 0 < ε) :
    ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, ↑t ⊆ s → (∑ i in t, ε' i) ≤ ε := by
  rcases hs.exists_pos_has_sum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
  refine' ⟨ε', hpos, fun t ht => _⟩
  rw [← sum_subtype_of_mem _ ht]
  refine' (sum_le_has_sum _ _ hε'c).trans hcε
  exact fun _ _ => (hpos _).le

namespace Nnreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0 } (hε : ε ≠ 0) ι [Encodable ι] :
    ∃ ε' : ι → ℝ≥0 , (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε :=
  let ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  let ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  ⟨fun i => ⟨ε' i, le_of_ltₓ <| hε' i⟩, fun i => Nnreal.coe_lt_coe.1 <| hε' i,
    ⟨c, has_sum_le (fun i => le_of_ltₓ <| hε' i) has_sum_zero hc⟩, Nnreal.has_sum_coe.1 hc,
    lt_of_le_of_ltₓ (Nnreal.coe_le_coe.1 hcε) aε⟩

end Nnreal

namespace Ennreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) ι [Encodable ι] :
    ∃ ε' : ι → ℝ≥0 , (∀ i, 0 < ε' i) ∧ (∑' i, (ε' i : ℝ≥0∞)) < ε := by
  rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
  rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩
  rcases Nnreal.exists_pos_sum_of_encodable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
  exact ⟨ε', hp, (Ennreal.tsum_coe_eq hc).symm ▸ lt_transₓ (coe_lt_coe.2 hcr) hrε⟩

theorem exists_pos_sum_of_encodable' {ε : ℝ≥0∞} (hε : ε ≠ 0) ι [Encodable ι] :
    ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ (∑' i, ε' i) < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_encodable hε ι
  ⟨fun i => δ i, fun i => Ennreal.coe_pos.2 (δpos i), hδ⟩

theorem exists_pos_tsum_mul_lt_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) {ι} [Encodable ι] (w : ι → ℝ≥0∞)
    (hw : ∀ i, w i ≠ ∞) : ∃ δ : ι → ℝ≥0 , (∀ i, 0 < δ i) ∧ (∑' i, (w i * δ i : ℝ≥0∞)) < ε := by
  lift w to ι → ℝ≥0 using hw
  rcases exists_pos_sum_of_encodable hε ι with ⟨δ', Hpos, Hsum⟩
  have : ∀ i, 0 < max 1 (w i) := fun i => zero_lt_one.trans_le (le_max_leftₓ _ _)
  refine' ⟨fun i => δ' i / max 1 (w i), fun i => Nnreal.div_pos (Hpos _) (this i), _⟩
  refine' lt_of_le_of_ltₓ (Ennreal.tsum_le_tsum fun i => _) Hsum
  rw [coe_div (this i).ne']
  refine' mul_le_of_le_div' (Ennreal.mul_le_mul le_rfl <| Ennreal.inv_le_inv.2 _)
  exact coe_le_coe.2 (le_max_rightₓ _ _)

end Ennreal

/-!
### Factorial
-/


theorem factorial_tendsto_at_top : Tendsto Nat.factorial atTop atTop :=
  tendsto_at_top_at_top_of_monotone Nat.monotone_factorial fun n => ⟨n, n.self_le_factorial⟩

theorem tendsto_factorial_div_pow_self_at_top : Tendsto (fun n => n ! / n ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_const_div_at_top_nhds_0_nat 1)
    (eventually_of_forall fun n =>
      div_nonneg
        (by
          exact_mod_cast n.factorial_pos.le)
        (pow_nonneg
          (by
            exact_mod_cast n.zero_le)
          _))
    (by
      refine' (eventually_gt_at_top 0).mono fun n hn => _
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [← prod_range_add_one_eq_factorial, pow_eq_prod_const, div_eq_mul_inv, ← inv_eq_one_div, prod_nat_cast,
        Nat.cast_succₓ, ← prod_inv_distrib', ← prod_mul_distrib, Finset.prod_range_succ']
      simp only [prod_range_succ', one_mulₓ, Nat.cast_addₓ, zero_addₓ, Nat.cast_oneₓ]
      refine'
          mul_le_of_le_one_left
            (inv_nonneg.mpr <| by
              exact_mod_cast hn.le)
            (prod_le_one _ _) <;>
        intro x hx <;> rw [Finset.mem_range] at hx
      · refine' mul_nonneg _ (inv_nonneg.mpr _) <;> norm_cast <;> linarith
        
      · refine'
          (div_le_one <| by
                exact_mod_cast hn).mpr
            _
        norm_cast
        linarith
        )

/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_field_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n => x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial extimates
  have A : (0 : ℝ) < ⌊∥x∥⌋₊ + 1 :=
    zero_lt_one.trans_le
      (by
        simp )
  have B : ∥x∥ / (⌊∥x∥⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊∥x∥⌋₊`.
  suffices : ∀, ∀ n ≥ ⌊∥x∥⌋₊, ∀, ∥x ^ (n + 1) / (n + 1)!∥ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / ↑n !∥
  exact summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨⌊∥x∥⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc ∥x ^ (n + 1) / (n + 1)!∥ = ∥x∥ / (n + 1) * ∥x ^ n / n !∥ := by
      rw [pow_succₓ, Nat.factorial_succ, Nat.cast_mulₓ, ← div_mul_div, norm_mul, norm_div, Real.norm_coe_nat,
        Nat.cast_succₓ]_ ≤ ∥x∥ / (⌊∥x∥⌋₊ + 1) * ∥x ^ n / n !∥ :=
      by
      mono* with 0 ≤ ∥x ^ n / n !∥, 0 ≤ ∥x∥ <;> apply norm_nonneg

theorem Real.tendsto_pow_div_factorial_at_top (x : ℝ) : Tendsto (fun n => x ^ n / n ! : ℕ → ℝ) atTop (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_at_top_zero

/-!
### Ceil and floor
-/


section

variable {R : Type _} [TopologicalSpace R] [LinearOrderedField R] [OrderTopology R] [FloorRing R]

theorem tendsto_nat_floor_mul_div_at_top {a : R} (ha : 0 ≤ a) : Tendsto (fun x => (⌊a * x⌋₊ : R) / x) atTop (𝓝 a) := by
  have A : tendsto (fun x : R => a - x⁻¹) at_top (𝓝 (a - 0)) := tendsto_const_nhds.sub tendsto_inv_at_top_zero
  rw [sub_zero] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    simp only [le_div_iff (zero_lt_one.trans_le hx), sub_mul, inv_mul_cancel (zero_lt_one.trans_le hx).ne']
    have := Nat.lt_floor_add_one (a * x)
    linarith
    
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    rw [div_le_iff (zero_lt_one.trans_le hx)]
    simp [Nat.floor_le (mul_nonneg ha (zero_le_one.trans hx))]
    

theorem tendsto_nat_ceil_mul_div_at_top {a : R} (ha : 0 ≤ a) : Tendsto (fun x => (⌈a * x⌉₊ : R) / x) atTop (𝓝 a) := by
  have A : tendsto (fun x : R => a + x⁻¹) at_top (𝓝 (a + 0)) := tendsto_const_nhds.add tendsto_inv_at_top_zero
  rw [add_zeroₓ] at A
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    rw [le_div_iff (zero_lt_one.trans_le hx)]
    exact Nat.le_ceil _
    
  · refine' eventually_at_top.2 ⟨1, fun x hx => _⟩
    simp [div_le_iff (zero_lt_one.trans_le hx), inv_mul_cancel (zero_lt_one.trans_le hx).ne',
      (Nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, add_mulₓ]
    

end

