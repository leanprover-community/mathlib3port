import Mathbin.Algebra.GeomSum 
import Mathbin.Analysis.Asymptotics.Asymptotics 
import Mathbin.Order.Filter.Archimedean 
import Mathbin.Order.Iterate 
import Mathbin.Topology.Instances.Ennreal

/-!
# A collection of specific limit computations
-/


noncomputable theory

open Classical Set Function Filter Finset Metric Asymptotics

open_locale Classical TopologicalSpace Nat BigOperators uniformity Nnreal Ennreal

variable{α : Type _}{β : Type _}{ι : Type _}

theorem tendsto_norm_at_top_at_top : tendsto (norm : ℝ → ℝ) at_top at_top :=
  tendsto_abs_at_top_at_top

theorem summable_of_absolute_convergence_real {f : ℕ → ℝ} :
  (∃ r, tendsto (fun n => ∑i in range n, |f i|) at_top (𝓝 r)) → Summable f
| ⟨r, hr⟩ =>
  by 
    refine' summable_of_summable_norm ⟨r, (has_sum_iff_tendsto_nat_of_nonneg _ _).2 _⟩
    exact fun i => norm_nonneg _ 
    simpa only using hr

theorem tendsto_inverse_at_top_nhds_0_nat : tendsto (fun n : ℕ => (n : ℝ)⁻¹) at_top (𝓝 0) :=
  tendsto_inv_at_top_zero.comp tendsto_coe_nat_at_top_at_top

theorem tendsto_const_div_at_top_nhds_0_nat (C : ℝ) : tendsto (fun n : ℕ => C / n) at_top (𝓝 0) :=
  by 
    simpa only [mul_zero] using tendsto_const_nhds.mul tendsto_inverse_at_top_nhds_0_nat

theorem Nnreal.tendsto_inverse_at_top_nhds_0_nat : tendsto (fun n : ℕ => (n :  ℝ≥0 )⁻¹) at_top (𝓝 0) :=
  by 
    rw [←Nnreal.tendsto_coe]
    convert tendsto_inverse_at_top_nhds_0_nat 
    simp 

theorem Nnreal.tendsto_const_div_at_top_nhds_0_nat (C :  ℝ≥0 ) : tendsto (fun n : ℕ => C / n) at_top (𝓝 0) :=
  by 
    simpa using tendsto_const_nhds.mul Nnreal.tendsto_inverse_at_top_nhds_0_nat

theorem tendsto_one_div_add_at_top_nhds_0_nat : tendsto (fun n : ℕ => 1 / (n : ℝ)+1) at_top (𝓝 0) :=
  suffices tendsto (fun n : ℕ => 1 / («expr↑ » (n+1) : ℝ)) at_top (𝓝 0)by 
    simpa
  (tendsto_add_at_top_iff_nat 1).2 (tendsto_const_div_at_top_nhds_0_nat 1)

/-! ### Powers -/


theorem tendsto_add_one_pow_at_top_at_top_of_pos [LinearOrderedSemiring α] [Archimedean α] {r : α} (h : 0 < r) :
  tendsto (fun n : ℕ => (r+1) ^ n) at_top at_top :=
  (tendsto_at_top_at_top_of_monotone' fun n m => pow_le_pow (le_add_of_nonneg_left (le_of_ltₓ h)))$
    not_bdd_above_iff.2$ fun x => Set.exists_range_iff.2$ add_one_pow_unbounded_of_pos _ h

theorem tendsto_pow_at_top_at_top_of_one_lt [LinearOrderedRing α] [Archimedean α] {r : α} (h : 1 < r) :
  tendsto (fun n : ℕ => r ^ n) at_top at_top :=
  sub_add_cancel r 1 ▸ tendsto_add_one_pow_at_top_at_top_of_pos (sub_pos.2 h)

theorem Nat.tendsto_pow_at_top_at_top_of_one_lt {m : ℕ} (h : 1 < m) : tendsto (fun n : ℕ => m ^ n) at_top at_top :=
  tsub_add_cancel_of_le (le_of_ltₓ h) ▸ tendsto_add_one_pow_at_top_at_top_of_pos (tsub_pos_of_lt h)

theorem tendsto_norm_zero' {𝕜 : Type _} [NormedGroup 𝕜] : tendsto (norm : 𝕜 → ℝ) (𝓝[«expr ᶜ» {0}] 0) (𝓝[Set.Ioi 0] 0) :=
  tendsto_norm_zero.inf$ tendsto_principal_principal.2$ fun x hx => norm_pos_iff.2 hx

namespace NormedField

theorem tendsto_norm_inverse_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] :
  tendsto (fun x : 𝕜 => ∥x⁻¹∥) (𝓝[«expr ᶜ» {0}] 0) at_top :=
  (tendsto_inv_zero_at_top.comp tendsto_norm_zero').congr$ fun x => (NormedField.norm_inv x).symm

theorem tendsto_norm_zpow_nhds_within_0_at_top {𝕜 : Type _} [NormedField 𝕜] {m : ℤ} (hm : m < 0) :
  tendsto (fun x : 𝕜 => ∥x ^ m∥) (𝓝[«expr ᶜ» {0}] 0) at_top :=
  by 
    rcases neg_surjective m with ⟨m, rfl⟩
    rw [neg_lt_zero] at hm 
    lift m to ℕ using hm.le 
    rw [Int.coe_nat_pos] at hm 
    simp only [NormedField.norm_pow, zpow_neg₀, zpow_coe_nat, ←inv_pow₀]
    exact (tendsto_pow_at_top hm).comp NormedField.tendsto_norm_inverse_nhds_within_0_at_top

@[simp]
theorem continuous_at_zpow {𝕜 : Type _} [NondiscreteNormedField 𝕜] {m : ℤ} {x : 𝕜} :
  ContinuousAt (fun x => x ^ m) x ↔ x ≠ 0 ∨ 0 ≤ m :=
  by 
    refine' ⟨_, continuous_at_zpow _ _⟩
    contrapose! 
    rintro ⟨rfl, hm⟩ hc 
    exact
      not_tendsto_at_top_of_tendsto_nhds (hc.tendsto.mono_left nhds_within_le_nhds).norm
        (tendsto_norm_zpow_nhds_within_0_at_top hm)

@[simp]
theorem continuous_at_inv {𝕜 : Type _} [NondiscreteNormedField 𝕜] {x : 𝕜} : ContinuousAt HasInv.inv x ↔ x ≠ 0 :=
  by 
    simpa [(@zero_lt_one ℤ _ _).not_le] using @continuous_at_zpow _ _ (-1) x

end NormedField

theorem tendsto_pow_at_top_nhds_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜] [TopologicalSpace 𝕜]
  [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 ≤ r) (h₂ : r < 1) : tendsto (fun n : ℕ => r ^ n) at_top (𝓝 0) :=
  h₁.eq_or_lt.elim
    (fun this : 0 = r =>
      (tendsto_add_at_top_iff_nat 1).mp$
        by 
          simp [pow_succₓ, ←this, tendsto_const_nhds])
    fun this : 0 < r =>
      have  : tendsto (fun n => (r⁻¹ ^ n)⁻¹) at_top (𝓝 0) :=
        tendsto_inv_at_top_zero.comp (tendsto_pow_at_top_at_top_of_one_lt$ one_lt_inv this h₂)
      this.congr
        fun n =>
          by 
            simp 

theorem tendsto_pow_at_top_nhds_within_0_of_lt_1 {𝕜 : Type _} [LinearOrderedField 𝕜] [Archimedean 𝕜]
  [TopologicalSpace 𝕜] [OrderTopology 𝕜] {r : 𝕜} (h₁ : 0 < r) (h₂ : r < 1) :
  tendsto (fun n : ℕ => r ^ n) at_top (𝓝[Ioi 0] 0) :=
  tendsto_inf.2
    ⟨tendsto_pow_at_top_nhds_0_of_lt_1 h₁.le h₂, tendsto_principal.2$ eventually_of_forall$ fun n => pow_pos h₁ _⟩

theorem is_o_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
  is_o (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) at_top :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (is_o_of_tendsto fun n hn => False.elim$ H.ne'$ pow_eq_zero hn)$
    (tendsto_pow_at_top_nhds_0_of_lt_1 (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr
      fun n => div_pow _ _ _

theorem is_O_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
  is_O (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) at_top :=
  h₂.eq_or_lt.elim (fun h => h ▸ is_O_refl _ _) fun h => (is_o_pow_pow_of_lt_left h₁ h).IsO

theorem is_o_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
  is_o (fun n : ℕ => r₁ ^ n) (fun n => r₂ ^ n) at_top :=
  by 
    refine' (is_o.of_norm_left _).of_norm_right 
    exact (is_o_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
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
theorem tfae_exists_lt_is_o_pow
(f : exprℕ() → exprℝ())
(R : exprℝ()) : tfae «expr[ , ]»([«expr∃ , »((a «expr ∈ » Ioo «expr- »(R) R), is_o f (pow a) at_top), «expr∃ , »((a «expr ∈ » Ioo 0 R), is_o f (pow a) at_top), «expr∃ , »((a «expr ∈ » Ioo «expr- »(R) R), is_O f (pow a) at_top), «expr∃ , »((a «expr ∈ » Ioo 0 R), is_O f (pow a) at_top), «expr∃ , »((a «expr < » R)
   (C)
   (h₀ : «expr ∨ »(«expr < »(0, C), «expr < »(0, R))), ∀
   n, «expr ≤ »(«expr| |»(f n), «expr * »(C, «expr ^ »(a, n)))), «expr∃ , »((a «expr ∈ » Ioo 0 R)
   (C «expr > » 0), ∀
   n, «expr ≤ »(«expr| |»(f n), «expr * »(C, «expr ^ »(a, n)))), «expr∃ , »((a «expr < » R), «expr∀ᶠ in , »((n), at_top, «expr ≤ »(«expr| |»(f n), «expr ^ »(a, n)))), «expr∃ , »((a «expr ∈ » Ioo 0 R), «expr∀ᶠ in , »((n), at_top, «expr ≤ »(«expr| |»(f n), «expr ^ »(a, n))))]) :=
begin
  have [ident A] [":", expr «expr ⊆ »(Ico 0 R, Ioo «expr- »(R) R)] [],
  from [expr λ x hx, ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩],
  have [ident B] [":", expr «expr ⊆ »(Ioo 0 R, Ioo «expr- »(R) R)] [":=", expr subset.trans Ioo_subset_Ico_self A],
  tfae_have [":"] [1] ["->"] [3],
  from [expr λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩],
  tfae_have [":"] [2] ["->"] [1],
  from [expr λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩],
  tfae_have [":"] [3] ["->"] [2],
  { rintro ["⟨", ident a, ",", ident ha, ",", ident H, "⟩"],
    rcases [expr exists_between (abs_lt.2 ha), "with", "⟨", ident b, ",", ident hab, ",", ident hbR, "⟩"],
    exact [expr ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩, H.trans_is_o (is_o_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩] },
  tfae_have [":"] [2] ["->"] [4],
  from [expr λ ⟨a, ha, H⟩, ⟨a, ha, H.is_O⟩],
  tfae_have [":"] [4] ["->"] [3],
  from [expr λ ⟨a, ha, H⟩, ⟨a, B ha, H⟩],
  tfae_have [":"] [4] ["->"] [6],
  { rintro ["⟨", ident a, ",", ident ha, ",", ident H, "⟩"],
    rcases [expr bound_of_is_O_nat_at_top H, "with", "⟨", ident C, ",", ident hC₀, ",", ident hC, "⟩"],
    refine [expr ⟨a, ha, C, hC₀, λ n, _⟩],
    simpa [] [] ["only"] ["[", expr real.norm_eq_abs, ",", expr abs_pow, ",", expr abs_of_nonneg ha.1.le, "]"] [] ["using", expr hC (pow_ne_zero n ha.1.ne')] },
  tfae_have [":"] [6] ["->"] [5],
  from [expr λ ⟨a, ha, C, H₀, H⟩, ⟨a, ha.2, C, or.inl H₀, H⟩],
  tfae_have [":"] [5] ["->"] [3],
  { rintro ["⟨", ident a, ",", ident ha, ",", ident C, ",", ident h₀, ",", ident H, "⟩"],
    rcases [expr sign_cases_of_C_mul_pow_nonneg (λ
      n, (abs_nonneg _).trans (H n)), "with", ident rfl, "|", "⟨", ident hC₀, ",", ident ha₀, "⟩"],
    { obtain [ident rfl, ":", expr «expr = »(f, 0)],
      by { ext [] [ident n] [],
        simpa [] [] [] [] [] ["using", expr H n] },
      simp [] [] ["only"] ["[", expr lt_irrefl, ",", expr false_or, "]"] [] ["at", ident h₀],
      exact [expr ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, is_O_zero _ _⟩] },
    exact [expr ⟨a, A ⟨ha₀, ha⟩, is_O_of_le' _ (λ
       n, «expr $ »((H n).trans, mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le))⟩] },
  tfae_have [":"] [2] ["->"] [8],
  { rintro ["⟨", ident a, ",", ident ha, ",", ident H, "⟩"],
    refine [expr ⟨a, ha, (H.def zero_lt_one).mono (λ n hn, _)⟩],
    rwa ["[", expr real.norm_eq_abs, ",", expr real.norm_eq_abs, ",", expr one_mul, ",", expr abs_pow, ",", expr abs_of_pos ha.1, "]"] ["at", ident hn] },
  tfae_have [":"] [8] ["->"] [7],
  from [expr λ ⟨a, ha, H⟩, ⟨a, ha.2, H⟩],
  tfae_have [":"] [7] ["->"] [3],
  { rintro ["⟨", ident a, ",", ident ha, ",", ident H, "⟩"],
    have [] [":", expr «expr ≤ »(0, a)] [],
    from [expr nonneg_of_eventually_pow_nonneg «expr $ »(H.mono, λ n, (abs_nonneg _).trans)],
    refine [expr ⟨a, A ⟨this, ha⟩, is_O.of_bound 1 _⟩],
    simpa [] [] ["only"] ["[", expr real.norm_eq_abs, ",", expr one_mul, ",", expr abs_pow, ",", expr abs_of_nonneg this, "]"] [] [] },
  tfae_finish
end

theorem uniformity_basis_dist_pow_of_lt_1 {α : Type _} [PseudoMetricSpace α] {r : ℝ} (h₀ : 0 < r) (h₁ : r < 1) :
  (𝓤 α).HasBasis (fun k : ℕ => True) fun k => { p:α × α | dist p.1 p.2 < r ^ k } :=
  (Metric.mk_uniformity_basis fun i _ => pow_pos h₀ _)$
    fun ε ε0 => (exists_pow_lt_of_lt_one ε0 h₁).imp$ fun k hk => ⟨trivialₓ, hk.le⟩

theorem geom_lt {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀ k _ : k < n, (c*u k) < u (k+1)) :
  ((c ^ n)*u 0) < u n :=
  by 
    refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_le_of_lt hn _ _ h
    ·
      simp 
    ·
      simp [pow_succₓ, mul_assocₓ, le_reflₓ]

theorem geom_le {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k _ : k < n, (c*u k) ≤ u (k+1)) : ((c ^ n)*u 0) ≤ u n :=
  by 
    refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ _ h <;> simp [pow_succₓ, mul_assocₓ, le_reflₓ]

theorem lt_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) {n : ℕ} (hn : 0 < n) (h : ∀ k _ : k < n, u (k+1) < c*u k) :
  u n < (c ^ n)*u 0 :=
  by 
    refine' (monotone_mul_left_of_nonneg hc).seq_pos_lt_seq_of_lt_of_le hn _ h _
    ·
      simp 
    ·
      simp [pow_succₓ, mul_assocₓ, le_reflₓ]

theorem le_geom {u : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (h : ∀ k _ : k < n, u (k+1) ≤ c*u k) : u n ≤ (c ^ n)*u 0 :=
  by 
    refine' (monotone_mul_left_of_nonneg hc).seq_le_seq n _ h _ <;> simp [pow_succₓ, mul_assocₓ, le_reflₓ]

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_const_pow_of_one_lt
{R : Type*}
[normed_ring R]
(k : exprℕ())
{r : exprℝ()}
(hr : «expr < »(1, r)) : is_o (λ n, «expr ^ »(n, k) : exprℕ() → R) (λ n, «expr ^ »(r, n)) at_top :=
begin
  have [] [":", expr tendsto (λ x : exprℝ(), «expr ^ »(x, k)) «expr𝓝[ ] »(Ioi 1, 1) (expr𝓝() 1)] [],
  from [expr ((continuous_id.pow k).tendsto' (1 : exprℝ()) 1 (one_pow _)).mono_left inf_le_left],
  obtain ["⟨", ident r', ":", expr exprℝ(), ",", ident hr', ":", expr «expr < »(«expr ^ »(r', k), r), ",", ident h1, ":", expr «expr < »(1, r'), "⟩", ":=", expr ((this.eventually (gt_mem_nhds hr)).and self_mem_nhds_within).exists],
  have [ident h0] [":", expr «expr ≤ »(0, r')] [":=", expr zero_le_one.trans h1.le],
  suffices [] [":", expr is_O _ (λ n : exprℕ(), «expr ^ »(«expr ^ »(r', k), n)) at_top],
  from [expr this.trans_is_o (is_o_pow_pow_of_lt_left (pow_nonneg h0 _) hr')],
  conv [] ["in", expr «expr ^ »(«expr ^ »(r', _), _)] { rw ["[", "<-", expr pow_mul, ",", expr mul_comm, ",", expr pow_mul, "]"] },
  suffices [] [":", expr ∀
   n : exprℕ(), «expr ≤ »(«expr∥ ∥»((n : R)), «expr * »(«expr * »(«expr ⁻¹»(«expr - »(r', 1)), «expr∥ ∥»((1 : R))), «expr∥ ∥»(«expr ^ »(r', n))))],
  from [expr (is_O_of_le' _ this).pow _],
  intro [ident n],
  rw [expr mul_right_comm] [],
  refine [expr n.norm_cast_le.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))],
  simpa [] [] [] ["[", expr div_eq_inv_mul, ",", expr real.norm_eq_abs, ",", expr abs_of_nonneg h0, "]"] [] ["using", expr n.cast_le_pow_div_sub h1]
end

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
theorem is_o_coe_const_pow_of_one_lt {R : Type _} [NormedRing R] {r : ℝ} (hr : 1 < r) :
  is_o (coeₓ : ℕ → R) (fun n => r ^ n) at_top :=
  by 
    simpa only [pow_oneₓ] using is_o_pow_const_const_pow_of_one_lt 1 hr

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `∥r₁∥ < r₂`, then for any naturak `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
theorem is_o_pow_const_mul_const_pow_const_pow_of_norm_lt
{R : Type*}
[normed_ring R]
(k : exprℕ())
{r₁ : R}
{r₂ : exprℝ()}
(h : «expr < »(«expr∥ ∥»(r₁), r₂)) : is_o (λ
n, «expr * »(«expr ^ »(n, k), «expr ^ »(r₁, n)) : exprℕ() → R) (λ n, «expr ^ »(r₂, n)) at_top :=
begin
  by_cases [expr h0, ":", expr «expr = »(r₁, 0)],
  { refine [expr (is_o_zero _ _).congr' «expr $ »(mem_at_top_sets.2, ⟨1, λ n hn, _⟩) eventually_eq.rfl],
    simp [] [] [] ["[", expr zero_pow (zero_lt_one.trans_le hn), ",", expr h0, "]"] [] [] },
  rw ["[", "<-", expr ne.def, ",", "<-", expr norm_pos_iff, "]"] ["at", ident h0],
  have [ident A] [":", expr is_o (λ
   n, «expr ^ »(n, k) : exprℕ() → R) (λ n, «expr ^ »(«expr / »(r₂, «expr∥ ∥»(r₁)), n)) at_top] [],
  from [expr is_o_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)],
  suffices [] [":", expr is_O (λ n, «expr ^ »(r₁, n)) (λ n, «expr ^ »(«expr∥ ∥»(r₁), n)) at_top],
  by simpa [] [] [] ["[", expr div_mul_cancel _ (pow_pos h0 _).ne', "]"] [] ["using", expr A.mul_is_O this],
  exact [expr is_O.of_bound 1 (by simpa [] [] [] [] [] ["using", expr eventually_norm_pow_le r₁])]
end

theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
  tendsto (fun n => n ^ k / r ^ n : ℕ → ℝ) at_top (𝓝 0) :=
  (is_o_pow_const_const_pow_of_one_lt k hr).tendsto_0

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one
(k : exprℕ())
{r : exprℝ()}
(hr : «expr < »(«expr| |»(r), 1)) : tendsto (λ
n, «expr * »(«expr ^ »(n, k), «expr ^ »(r, n)) : exprℕ() → exprℝ()) at_top (expr𝓝() 0) :=
begin
  by_cases [expr h0, ":", expr «expr = »(r, 0)],
  { exact [expr tendsto_const_nhds.congr' (mem_at_top_sets.2 ⟨1, λ
       n hn, by simp [] [] [] ["[", expr zero_lt_one.trans_le hn, ",", expr h0, "]"] [] []⟩)] },
  have [ident hr'] [":", expr «expr < »(1, «expr ⁻¹»(«expr| |»(r)))] [],
  from [expr one_lt_inv (abs_pos.2 h0) hr],
  rw [expr tendsto_zero_iff_norm_tendsto_zero] [],
  simpa [] [] [] ["[", expr div_eq_mul_inv, "]"] [] ["using", expr tendsto_pow_const_div_const_pow_of_one_lt k hr']
end

/-- If a sequence `v` of real numbers satisfies `k * v n ≤ v (n+1)` with `1 < k`,
then it goes to +∞. -/
theorem tendsto_at_top_of_geom_le {v : ℕ → ℝ} {c : ℝ} (h₀ : 0 < v 0) (hc : 1 < c) (hu : ∀ n, (c*v n) ≤ v (n+1)) :
  tendsto v at_top at_top :=
  (tendsto_at_top_mono fun n => geom_le (zero_le_one.trans hc.le) n fun k hk => hu k)$
    (tendsto_pow_at_top_at_top_of_one_lt hc).at_top_mul_const h₀

theorem Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r :  ℝ≥0 } (hr : r < 1) : tendsto (fun n : ℕ => r ^ n) at_top (𝓝 0) :=
  Nnreal.tendsto_coe.1$
    by 
      simp only [Nnreal.coe_pow, Nnreal.coe_zero, tendsto_pow_at_top_nhds_0_of_lt_1 r.coe_nonneg hr]

theorem Ennreal.tendsto_pow_at_top_nhds_0_of_lt_1 {r : ℝ≥0∞} (hr : r < 1) : tendsto (fun n : ℕ => r ^ n) at_top (𝓝 0) :=
  by 
    rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
    rw [←Ennreal.coe_zero]
    normCast  at *
    apply Nnreal.tendsto_pow_at_top_nhds_0_of_lt_1 hr

/-- In a normed ring, the powers of an element x with `∥x∥ < 1` tend to zero. -/
theorem tendsto_pow_at_top_nhds_0_of_norm_lt_1 {R : Type _} [NormedRing R] {x : R} (h : ∥x∥ < 1) :
  tendsto (fun n : ℕ => x ^ n) at_top (𝓝 0) :=
  by 
    apply squeeze_zero_norm' (eventually_norm_pow_le x)
    exact tendsto_pow_at_top_nhds_0_of_lt_1 (norm_nonneg _) h

theorem tendsto_pow_at_top_nhds_0_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : tendsto (fun n : ℕ => r ^ n) at_top (𝓝 0) :=
  tendsto_pow_at_top_nhds_0_of_norm_lt_1 h

/-! ### Geometric series-/


section Geometric

theorem has_sum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : HasSum (fun n : ℕ => r ^ n) ((1 - r)⁻¹) :=
  have  : r ≠ 1 := ne_of_ltₓ h₂ 
  have  : tendsto (fun n => (r ^ n - 1)*(r - 1)⁻¹) at_top (𝓝 ((0 - 1)*(r - 1)⁻¹)) :=
    ((tendsto_pow_at_top_nhds_0_of_lt_1 h₁ h₂).sub tendsto_const_nhds).mul tendsto_const_nhds 
  have  : (fun n => ∑i in range n, r ^ i) = fun n => geomSum r n := rfl
  (has_sum_iff_tendsto_nat_of_nonneg (pow_nonneg h₁) _).mpr$
    by 
      simp_all [neg_inv, geom_sum_eq, div_eq_mul_inv]

theorem summable_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, has_sum_geometric_of_lt_1 h₁ h₂⟩

theorem tsum_geometric_of_lt_1 {r : ℝ} (h₁ : 0 ≤ r) (h₂ : r < 1) : (∑'n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (has_sum_geometric_of_lt_1 h₁ h₂).tsum_eq

theorem has_sum_geometric_two : HasSum (fun n : ℕ => ((1 : ℝ) / 2) ^ n) 2 :=
  by 
    convert has_sum_geometric_of_lt_1 _ _ <;> normNum

theorem summable_geometric_two : Summable fun n : ℕ => ((1 : ℝ) / 2) ^ n :=
  ⟨_, has_sum_geometric_two⟩

theorem tsum_geometric_two : (∑'n : ℕ, ((1 : ℝ) / 2) ^ n) = 2 :=
  has_sum_geometric_two.tsum_eq

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_geometric_two_le
(n : exprℕ()) : «expr ≤ »(«expr∑ in , »((i : exprℕ()), range n, «expr ^ »(«expr / »(1, (2 : exprℝ())), i)), 2) :=
begin
  have [] [":", expr ∀ i, «expr ≤ »(0, «expr ^ »(«expr / »(1, (2 : exprℝ())), i))] [],
  { intro [ident i],
    apply [expr pow_nonneg],
    norm_num [] [] },
  convert [] [expr sum_le_tsum (range n) (λ i _, this i) summable_geometric_two] [],
  exact [expr tsum_geometric_two.symm]
end

theorem has_sum_geometric_two' (a : ℝ) : HasSum (fun n : ℕ => a / 2 / 2 ^ n) a :=
  by 
    convert HasSum.mul_left (a / 2) (has_sum_geometric_of_lt_1 (le_of_ltₓ one_half_pos) one_half_lt_one)
    ·
      funext n 
      simp 
      rfl
    ·
      normNum

theorem summable_geometric_two' (a : ℝ) : Summable fun n : ℕ => a / 2 / 2 ^ n :=
  ⟨a, has_sum_geometric_two' a⟩

theorem tsum_geometric_two' (a : ℝ) : (∑'n : ℕ, a / 2 / 2 ^ n) = a :=
  (has_sum_geometric_two' a).tsum_eq

/-- **Sum of a Geometric Series** -/
theorem Nnreal.has_sum_geometric {r :  ℝ≥0 } (hr : r < 1) : HasSum (fun n : ℕ => r ^ n) ((1 - r)⁻¹) :=
  by 
    apply Nnreal.has_sum_coe.1
    pushCast 
    rw [Nnreal.coe_sub (le_of_ltₓ hr)]
    exact has_sum_geometric_of_lt_1 r.coe_nonneg hr

theorem Nnreal.summable_geometric {r :  ℝ≥0 } (hr : r < 1) : Summable fun n : ℕ => r ^ n :=
  ⟨_, Nnreal.has_sum_geometric hr⟩

theorem tsum_geometric_nnreal {r :  ℝ≥0 } (hr : r < 1) : (∑'n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  (Nnreal.has_sum_geometric hr).tsum_eq

/-- The series `pow r` converges to `(1-r)⁻¹`. For `r < 1` the RHS is a finite number,
and for `1 ≤ r` the RHS equals `∞`. -/
@[simp]
theorem Ennreal.tsum_geometric (r : ℝ≥0∞) : (∑'n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  by 
    cases' lt_or_leₓ r 1 with hr hr
    ·
      rcases Ennreal.lt_iff_exists_coe.1 hr with ⟨r, rfl, hr'⟩
      normCast  at *
      convert Ennreal.tsum_coe_eq (Nnreal.has_sum_geometric hr)
      rw [Ennreal.coe_inv$ ne_of_gtₓ$ tsub_pos_iff_lt.2 hr]
    ·
      rw [tsub_eq_zero_iff_le.mpr hr, Ennreal.inv_zero, Ennreal.tsum_eq_supr_nat, supr_eq_top]
      refine' fun a ha => (Ennreal.exists_nat_gt (lt_top_iff_ne_top.1 ha)).imp fun n hn => lt_of_lt_of_leₓ hn _ 
      calc (n : ℝ≥0∞) = ∑i in range n, 1 :=
        by 
          rw [sum_const, nsmul_one, card_range]_ ≤ ∑i in range n, r ^ i :=
        sum_le_sum fun k _ => one_le_pow_of_one_le' hr k

variable{K : Type _}[NormedField K]{ξ : K}

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem has_sum_geometric_of_norm_lt_1
(h : «expr < »(«expr∥ ∥»(ξ), 1)) : has_sum (λ n : exprℕ(), «expr ^ »(ξ, n)) «expr ⁻¹»(«expr - »(1, ξ)) :=
begin
  have [ident xi_ne_one] [":", expr «expr ≠ »(ξ, 1)] [],
  by { contrapose ["!"] [ident h],
    simp [] [] [] ["[", expr h, "]"] [] [] },
  have [ident A] [":", expr tendsto (λ
    n, «expr * »(«expr - »(«expr ^ »(ξ, n), 1), «expr ⁻¹»(«expr - »(ξ, 1)))) at_top (expr𝓝() «expr * »(«expr - »(0, 1), «expr ⁻¹»(«expr - »(ξ, 1))))] [],
  from [expr ((tendsto_pow_at_top_nhds_0_of_norm_lt_1 h).sub tendsto_const_nhds).mul tendsto_const_nhds],
  have [ident B] [":", expr «expr = »(λ
    n, «expr∑ in , »((i), range n, «expr ^ »(ξ, i)), λ n, geom_sum ξ n)] [":=", expr rfl],
  rw ["[", expr has_sum_iff_tendsto_nat_of_summable_norm, ",", expr B, "]"] [],
  { simpa [] [] [] ["[", expr geom_sum_eq, ",", expr xi_ne_one, ",", expr neg_inv, ",", expr div_eq_mul_inv, "]"] [] ["using", expr A] },
  { simp [] [] [] ["[", expr normed_field.norm_pow, ",", expr summable_geometric_of_lt_1 (norm_nonneg _) h, "]"] [] [] }
end

theorem summable_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : Summable fun n : ℕ => ξ ^ n :=
  ⟨_, has_sum_geometric_of_norm_lt_1 h⟩

theorem tsum_geometric_of_norm_lt_1 (h : ∥ξ∥ < 1) : (∑'n : ℕ, ξ ^ n) = (1 - ξ)⁻¹ :=
  (has_sum_geometric_of_norm_lt_1 h).tsum_eq

theorem has_sum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : HasSum (fun n : ℕ => r ^ n) ((1 - r)⁻¹) :=
  has_sum_geometric_of_norm_lt_1 h

theorem summable_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ => r ^ n :=
  summable_geometric_of_norm_lt_1 h

theorem tsum_geometric_of_abs_lt_1 {r : ℝ} (h : |r| < 1) : (∑'n : ℕ, r ^ n) = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_1 h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
theorem summable_geometric_iff_norm_lt_1 : (Summable fun n : ℕ => ξ ^ n) ↔ ∥ξ∥ < 1 :=
  by 
    refine' ⟨fun h => _, summable_geometric_of_norm_lt_1⟩
    obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
      (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists 
    simp only [NormedField.norm_pow, dist_zero_right] at hk 
    rw [←one_pow k] at hk 
    exact lt_of_pow_lt_pow _ zero_le_one hk

end Geometric

section MulGeometric

theorem summable_norm_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] (k : ℕ) {r : R} (hr : ∥r∥ < 1) :
  Summable fun n : ℕ => ∥((n ^ k)*r ^ n : R)∥ :=
  by 
    rcases exists_between hr with ⟨r', hrr', h⟩
    exact
      summable_of_is_O_nat (summable_geometric_of_lt_1 ((norm_nonneg _).trans hrr'.le) h)
        (is_o_pow_const_mul_const_pow_const_pow_of_norm_lt _ hrr').IsO.norm_left

theorem summable_pow_mul_geometric_of_norm_lt_1 {R : Type _} [NormedRing R] [CompleteSpace R] (k : ℕ) {r : R}
  (hr : ∥r∥ < 1) : Summable (fun n => (n ^ k)*r ^ n : ℕ → R) :=
  summable_of_summable_norm$ summable_norm_pow_mul_geometric_of_norm_lt_1 _ hr

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `has_sum` version. -/
theorem has_sum_coe_mul_geometric_of_norm_lt_1
{𝕜 : Type*}
[normed_field 𝕜]
[complete_space 𝕜]
{r : 𝕜}
(hr : «expr < »(«expr∥ ∥»(r), 1)) : has_sum (λ
n, «expr * »(n, «expr ^ »(r, n)) : exprℕ() → 𝕜) «expr / »(r, «expr ^ »(«expr - »(1, r), 2)) :=
begin
  have [ident A] [":", expr summable (λ n, «expr * »(n, «expr ^ »(r, n)) : exprℕ() → 𝕜)] [],
  by simpa [] [] [] [] [] ["using", expr summable_pow_mul_geometric_of_norm_lt_1 1 hr],
  have [ident B] [":", expr has_sum (pow r : exprℕ() → 𝕜) «expr ⁻¹»(«expr - »(1, r))] [],
  from [expr has_sum_geometric_of_norm_lt_1 hr],
  refine [expr A.has_sum_iff.2 _],
  have [ident hr'] [":", expr «expr ≠ »(r, 1)] [],
  by { rintro [ident rfl],
    simpa [] [] [] ["[", expr lt_irrefl, "]"] [] ["using", expr hr] },
  set [] [ident s] [":", expr 𝕜] [":="] [expr «expr∑' , »((n : exprℕ()), «expr * »(n, «expr ^ »(r, n)))] [],
  calc
    «expr = »(s, «expr / »(«expr * »(«expr - »(1, r), s), «expr - »(1, r))) : (mul_div_cancel_left _ (sub_ne_zero.2 hr'.symm)).symm
    «expr = »(..., «expr / »(«expr - »(s, «expr * »(r, s)), «expr - »(1, r))) : by rw ["[", expr sub_mul, ",", expr one_mul, "]"] []
    «expr = »(..., «expr / »(«expr - »(«expr + »(«expr * »((0 : exprℕ()), «expr ^ »(r, 0)), «expr∑' , »((n : exprℕ()), «expr * »(«expr + »(n, 1), «expr ^ »(r, «expr + »(n, 1))))), «expr * »(r, s)), «expr - »(1, r))) : by { congr,
      exact [expr tsum_eq_zero_add A] }
    «expr = »(..., «expr / »(«expr - »(«expr * »(r, «expr∑' , »((n : exprℕ()), «expr * »(«expr + »(n, 1), «expr ^ »(r, n)))), «expr * »(r, s)), «expr - »(1, r))) : by simp [] [] [] ["[", expr pow_succ, ",", expr mul_left_comm _ r, ",", expr tsum_mul_left, "]"] [] []
    «expr = »(..., «expr / »(r, «expr ^ »(«expr - »(1, r), 2))) : by simp [] [] [] ["[", expr add_mul, ",", expr tsum_add A B.summable, ",", expr mul_add, ",", expr B.tsum_eq, ",", "<-", expr div_eq_mul_inv, ",", expr sq, ",", expr div_div_eq_div_mul, "]"] [] []
end

/-- If `∥r∥ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
theorem tsum_coe_mul_geometric_of_norm_lt_1 {𝕜 : Type _} [NormedField 𝕜] [CompleteSpace 𝕜] {r : 𝕜} (hr : ∥r∥ < 1) :
  (∑'n : ℕ, n*r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
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

variable[PseudoEmetricSpace α](r C : ℝ≥0∞)(hr : r < 1)(hC : C ≠ ⊤){f : ℕ → α}(hu : ∀ n, edist (f n) (f (n+1)) ≤ C*r ^ n)

include hr hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, `C ≠ ∞`, `r < 1`,
then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric : CauchySeq f :=
  by 
    refine' cauchy_seq_of_edist_le_of_tsum_ne_top _ hu _ 
    rw [Ennreal.tsum_mul_left, Ennreal.tsum_geometric]
    refine' Ennreal.mul_ne_top hC (Ennreal.inv_ne_top.2 _)
    exact (tsub_pos_iff_lt.2 hr).ne'

omit hr hC

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  edist (f n) a ≤ (C*r ^ n) / (1 - r) :=
  by 
    convert edist_le_tsum_of_edist_le_of_tendsto _ hu ha _ 
    simp only [pow_addₓ, Ennreal.tsum_mul_left, Ennreal.tsum_geometric, div_eq_mul_inv, mul_assocₓ]

/-- If `edist (f n) (f (n+1))` is bounded by `C * r^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem edist_le_of_edist_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) :
  edist (f 0) a ≤ C / (1 - r) :=
  by 
    simpa only [pow_zeroₓ, mul_oneₓ] using edist_le_of_edist_le_geometric_of_tendsto r C hu ha 0

end EdistLeGeometric

section EdistLeGeometricTwo

variable[PseudoEmetricSpace
      α](C :
    ℝ≥0∞)(hC : C ≠ ⊤){f : ℕ → α}(hu : ∀ n, edist (f n) (f (n+1)) ≤ C / 2 ^ n){a : α}(ha : tendsto f at_top (𝓝 a))

include hC hu

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then `f` is a Cauchy sequence.-/
theorem cauchy_seq_of_edist_le_geometric_two : CauchySeq f :=
  by 
    simp only [div_eq_mul_inv, Ennreal.inv_pow] at hu 
    refine' cauchy_seq_of_edist_le_geometric (2⁻¹) C _ hC hu 
    simp [Ennreal.one_lt_two]

omit hC

include ha

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f n` to the limit of `f` is bounded above by `2 * C * 2^-n`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto (n : ℕ) : edist (f n) a ≤ (2*C) / 2 ^ n :=
  by 
    simp only [div_eq_mul_inv, Ennreal.inv_pow] at *
    rw [mul_assocₓ, mul_commₓ]
    convert edist_le_of_edist_le_geometric_of_tendsto (2⁻¹) C hu ha n 
    rw [Ennreal.one_sub_inv_two, Ennreal.inv_inv]

/-- If `edist (f n) (f (n+1))` is bounded by `C * 2^-n`, then the distance from
`f 0` to the limit of `f` is bounded above by `2 * C`. -/
theorem edist_le_of_edist_le_geometric_two_of_tendsto₀ : edist (f 0) a ≤ 2*C :=
  by 
    simpa only [pow_zeroₓ, div_eq_mul_inv, Ennreal.inv_one, mul_oneₓ] using
      edist_le_of_edist_le_geometric_two_of_tendsto C hu ha 0

end EdistLeGeometricTwo

section LeGeometric

variable[PseudoMetricSpace α]{r C : ℝ}(hr : r < 1){f : ℕ → α}(hu : ∀ n, dist (f n) (f (n+1)) ≤ C*r ^ n)

include hr hu

theorem aux_has_sum_of_le_geometric : HasSum (fun n : ℕ => C*r ^ n) (C / (1 - r)) :=
  by 
    rcases sign_cases_of_C_mul_pow_nonneg fun n => dist_nonneg.trans (hu n) with (rfl | ⟨C₀, r₀⟩)
    ·
      simp [has_sum_zero]
    ·
      refine' HasSum.mul_left C _ 
      simpa using has_sum_geometric_of_lt_1 r₀ hr

variable(r C)

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then `f` is a Cauchy sequence.
Note that this lemma does not assume `0 ≤ C` or `0 ≤ r`. -/
theorem cauchy_seq_of_le_geometric : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩

/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f n` to the limit of `f` is bounded above by `C * r^n / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) : dist (f 0) a ≤ C / (1 - r) :=
  (aux_has_sum_of_le_geometric hr hu).tsum_eq ▸
    dist_le_tsum_of_dist_le_of_tendsto₀ _ hu ⟨_, aux_has_sum_of_le_geometric hr hu⟩ ha

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- If `dist (f n) (f (n+1))` is bounded by `C * r^n`, `r < 1`, then the distance from
`f 0` to the limit of `f` is bounded above by `C / (1 - r)`. -/
theorem dist_le_of_le_geometric_of_tendsto
{a : α}
(ha : tendsto f at_top (expr𝓝() a))
(n : exprℕ()) : «expr ≤ »(dist (f n) a, «expr / »(«expr * »(C, «expr ^ »(r, n)), «expr - »(1, r))) :=
begin
  have [] [] [":=", expr aux_has_sum_of_le_geometric hr hu],
  convert [] [expr dist_le_tsum_of_dist_le_of_tendsto _ hu ⟨_, this⟩ ha n] [],
  simp [] [] ["only"] ["[", expr pow_add, ",", expr mul_left_comm C, ",", expr mul_div_right_comm, "]"] [] [],
  rw ["[", expr mul_comm, "]"] [],
  exact [expr (this.mul_left _).tsum_eq.symm]
end

omit hr hu

variable(hu₂ : ∀ n, dist (f n) (f (n+1)) ≤ C / 2 / 2 ^ n)

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then `f` is a Cauchy sequence. -/
theorem cauchy_seq_of_le_geometric_two : CauchySeq f :=
  cauchy_seq_of_dist_le_of_summable _ hu₂$ ⟨_, has_sum_geometric_two' C⟩

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f 0` to the limit of `f` is bounded above by `C`. -/
theorem dist_le_of_le_geometric_two_of_tendsto₀ {a : α} (ha : tendsto f at_top (𝓝 a)) : dist (f 0) a ≤ C :=
  tsum_geometric_two' C ▸ dist_le_tsum_of_dist_le_of_tendsto₀ _ hu₂ (summable_geometric_two' C) ha

include hu₂

/-- If `dist (f n) (f (n+1))` is bounded by `(C / 2) / 2^n`, then the distance from
`f n` to the limit of `f` is bounded above by `C / 2^n`. -/
theorem dist_le_of_le_geometric_two_of_tendsto {a : α} (ha : tendsto f at_top (𝓝 a)) (n : ℕ) :
  dist (f n) a ≤ C / 2 ^ n :=
  by 
    convert dist_le_tsum_of_dist_le_of_tendsto _ hu₂ (summable_geometric_two' C) ha n 
    simp only [add_commₓ n, pow_addₓ, ←div_div_eq_div_mul]
    symm 
    exact ((has_sum_geometric_two' C).div_const _).tsum_eq

end LeGeometric

section SummableLeGeometric

variable[SemiNormedGroup α]{r C : ℝ}{f : ℕ → α}

theorem SemiNormedGroup.cauchy_seq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1) {u : ℕ → α}
  (h : ∀ n, ∥u n - u (n+1)∥ ≤ C*r ^ n) : CauchySeq u :=
  cauchy_seq_of_le_geometric r C hr
    (by 
      simpa [dist_eq_norm] using h)

theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ∥f n∥ ≤ C*r ^ n) (n : ℕ) :
  dist (∑i in range n, f i) (∑i in range (n+1), f i) ≤ C*r ^ n :=
  by 
    rw [sum_range_succ, dist_eq_norm, ←norm_neg, neg_sub, add_sub_cancel']
    exact hf n

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
theorem cauchy_seq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C*r ^ n) :
  CauchySeq fun s : Finset ℕ => ∑x in s, f x :=
  cauchy_seq_finset_of_norm_bounded _ (aux_has_sum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).Summable
    hf

/-- If `∥f n∥ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
theorem norm_sub_le_of_geometric_bound_of_has_sum (hr : r < 1) (hf : ∀ n, ∥f n∥ ≤ C*r ^ n) {a : α} (ha : HasSum f a)
  (n : ℕ) : ∥(∑x in Finset.range n, f x) - a∥ ≤ (C*r ^ n) / (1 - r) :=
  by 
    rw [←dist_eq_norm]
    apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
    exact ha.tendsto_sum_nat

@[simp]
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) : dist (∑k in range (n+1), u k) (∑k in range n, u k) = ∥u n∥ :=
  by 
    simp [dist_eq_norm, sum_range_succ]

@[simp]
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) : dist (∑k in range n, u k) (∑k in range (n+1), u k) = ∥u n∥ :=
  by 
    simp [dist_eq_norm', sum_range_succ]

theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1) (h : ∀ n, ∥u n∥ ≤ C*r ^ n) :
  CauchySeq fun n => ∑k in range n, u k :=
  cauchy_seq_of_le_geometric r C hr
    (by 
      simp [h])

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normed_group.cauchy_series_of_le_geometric'
{C : exprℝ()}
{u : exprℕ() → α}
{r : exprℝ()}
(hr : «expr < »(r, 1))
(h : ∀
 n, «expr ≤ »(«expr∥ ∥»(u n), «expr * »(C, «expr ^ »(r, n)))) : cauchy_seq (λ
 n, «expr∑ in , »((k), range «expr + »(n, 1), u k)) :=
begin
  by_cases [expr hC, ":", expr «expr = »(C, 0)],
  { subst [expr hC],
    simp [] [] [] [] [] ["at", ident h],
    exact [expr cauchy_seq_of_le_geometric 0 0 zero_lt_one (by simp [] [] [] ["[", expr h, "]"] [] [])] },
  have [] [":", expr «expr ≤ »(0, C)] [],
  { simpa [] [] [] [] [] ["using", expr (norm_nonneg _).trans (h 0)] },
  replace [ident hC] [":", expr «expr < »(0, C)] [],
  from [expr (ne.symm hC).le_iff_lt.mp this],
  have [] [":", expr «expr ≤ »(0, r)] [],
  { have [] [] [":=", expr (norm_nonneg _).trans (h 1)],
    rw [expr pow_one] ["at", ident this],
    exact [expr (zero_le_mul_left hC).mp this] },
  simp_rw [expr finset.sum_range_succ_comm] [],
  have [] [":", expr cauchy_seq u] [],
  { apply [expr tendsto.cauchy_seq],
    apply [expr squeeze_zero_norm h],
    rw [expr show «expr = »(0, «expr * »(C, 0)), by simp [] [] [] [] [] []] [],
    exact [expr tendsto_const_nhds.mul (tendsto_pow_at_top_nhds_0_of_lt_1 this hr)] },
  exact [expr this.add (cauchy_series_of_le_geometric hr h)]
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem normed_group.cauchy_series_of_le_geometric''
{C : exprℝ()}
{u : exprℕ() → α}
{N : exprℕ()}
{r : exprℝ()}
(hr₀ : «expr < »(0, r))
(hr₁ : «expr < »(r, 1))
(h : ∀
 n «expr ≥ » N, «expr ≤ »(«expr∥ ∥»(u n), «expr * »(C, «expr ^ »(r, n)))) : cauchy_seq (λ
 n, «expr∑ in , »((k), range «expr + »(n, 1), u k)) :=
begin
  set [] [ident v] [":", expr exprℕ() → α] [":="] [expr λ n, if «expr < »(n, N) then 0 else u n] [],
  have [ident hC] [":", expr «expr ≤ »(0, C)] [],
  from [expr «expr $ »(zero_le_mul_right, pow_pos hr₀ N).mp «expr $ »((norm_nonneg _).trans, «expr $ »(h N, le_refl N))],
  have [] [":", expr ∀ n «expr ≥ » N, «expr = »(u n, v n)] [],
  { intros [ident n, ident hn],
    simp [] [] [] ["[", expr v, ",", expr hn, ",", expr if_neg (not_lt.mpr hn), "]"] [] [] },
  refine [expr cauchy_seq_sum_of_eventually_eq this (normed_group.cauchy_series_of_le_geometric' hr₁ _)],
  { exact [expr C] },
  intro [ident n],
  dsimp [] ["[", expr v, "]"] [] [],
  split_ifs [] ["with", ident H, ident H],
  { rw [expr norm_zero] [],
    exact [expr mul_nonneg hC (pow_nonneg hr₀.le _)] },
  { push_neg ["at", ident H],
    exact [expr h _ H] }
end

end SummableLeGeometric

section NormedRingGeometric

variable{R : Type _}[NormedRing R][CompleteSpace R]

open NormedSpace

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- A geometric series in a complete normed ring is summable.
Proved above (same name, different namespace) for not-necessarily-complete normed fields. -/
theorem normed_ring.summable_geometric_of_norm_lt_1
(x : R)
(h : «expr < »(«expr∥ ∥»(x), 1)) : summable (λ n : exprℕ(), «expr ^ »(x, n)) :=
begin
  have [ident h1] [":", expr summable (λ
    n : exprℕ(), «expr ^ »(«expr∥ ∥»(x), n))] [":=", expr summable_geometric_of_lt_1 (norm_nonneg _) h],
  refine [expr summable_of_norm_bounded_eventually _ h1 _],
  rw [expr nat.cofinite_eq_at_top] [],
  exact [expr eventually_norm_pow_le x]
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Bound for the sum of a geometric series in a normed ring.  This formula does not assume that the
normed ring satisfies the axiom `∥1∥ = 1`. -/
theorem normed_ring.tsum_geometric_of_norm_lt_1
(x : R)
(h : «expr < »(«expr∥ ∥»(x), 1)) : «expr ≤ »(«expr∥ ∥»(«expr∑' , »((n : exprℕ()), «expr ^ »(x, n))), «expr + »(«expr - »(«expr∥ ∥»((1 : R)), 1), «expr ⁻¹»(«expr - »(1, «expr∥ ∥»(x))))) :=
begin
  rw [expr tsum_eq_zero_add (normed_ring.summable_geometric_of_norm_lt_1 x h)] [],
  simp [] [] ["only"] ["[", expr pow_zero, "]"] [] [],
  refine [expr le_trans (norm_add_le _ _) _],
  have [] [":", expr «expr ≤ »(«expr∥ ∥»(«expr∑' , »((b : exprℕ()), λ
      n, «expr ^ »(x, «expr + »(n, 1)) b)), «expr - »(«expr ⁻¹»(«expr - »(1, «expr∥ ∥»(x))), 1))] [],
  { refine [expr tsum_of_norm_bounded _ (λ b, norm_pow_le' _ (nat.succ_pos b))],
    convert [] [expr (has_sum_nat_add_iff' 1).mpr (has_sum_geometric_of_lt_1 (norm_nonneg x) h)] [],
    simp [] [] [] [] [] [] },
  linarith [] [] []
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem geom_series_mul_neg
(x : R)
(h : «expr < »(«expr∥ ∥»(x), 1)) : «expr = »(«expr * »(«expr∑' , »((i : exprℕ()), «expr ^ »(x, i)), «expr - »(1, x)), 1) :=
begin
  have [] [] [":=", expr (normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_right «expr - »(1, x)],
  refine [expr tendsto_nhds_unique this.tendsto_sum_nat _],
  have [] [":", expr tendsto (λ n : exprℕ(), «expr - »(1, «expr ^ »(x, n))) at_top (expr𝓝() 1)] [],
  { simpa [] [] [] [] [] ["using", expr tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)] },
  convert ["<-"] [expr this] [],
  ext [] [ident n] [],
  rw ["[", "<-", expr geom_sum_mul_neg, ",", expr geom_sum_def, ",", expr finset.sum_mul, "]"] []
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem mul_neg_geom_series
(x : R)
(h : «expr < »(«expr∥ ∥»(x), 1)) : «expr = »(«expr * »(«expr - »(1, x), «expr∑' , »((i : exprℕ()), «expr ^ »(x, i))), 1) :=
begin
  have [] [] [":=", expr (normed_ring.summable_geometric_of_norm_lt_1 x h).has_sum.mul_left «expr - »(1, x)],
  refine [expr tendsto_nhds_unique this.tendsto_sum_nat _],
  have [] [":", expr tendsto (λ n : exprℕ(), «expr - »(1, «expr ^ »(x, n))) at_top (nhds 1)] [],
  { simpa [] [] [] [] [] ["using", expr tendsto_const_nhds.sub (tendsto_pow_at_top_nhds_0_of_norm_lt_1 h)] },
  convert ["<-"] [expr this] [],
  ext [] [ident n] [],
  rw ["[", "<-", expr mul_neg_geom_sum, ",", expr geom_sum_def, ",", expr finset.mul_sum, "]"] []
end

end NormedRingGeometric

/-! ### Summability tests based on comparison with geometric series -/


theorem summable_of_ratio_norm_eventually_le {α : Type _} [SemiNormedGroup α] [CompleteSpace α] {f : ℕ → α} {r : ℝ}
  (hr₁ : r < 1) (h : ∀ᶠn in at_top, ∥f (n+1)∥ ≤ r*∥f n∥) : Summable f :=
  by 
    byCases' hr₀ : 0 ≤ r
    ·
      rw [eventually_at_top] at h 
      rcases h with ⟨N, hN⟩
      rw [←@summable_nat_add_iff α _ _ _ _ N]
      refine'
        summable_of_norm_bounded (fun n => ∥f N∥*r ^ n) (Summable.mul_left _$ summable_geometric_of_lt_1 hr₀ hr₁)
          fun n => _ 
      convRHS => rw [mul_commₓ, ←zero_addₓ N]
      refine' le_geom hr₀ n fun i _ => _ 
      convert hN (i+N) (N.le_add_left i) using 3
      acRfl
    ·
      pushNeg  at hr₀ 
      refine' summable_of_norm_bounded_eventually 0 summable_zero _ 
      rw [Nat.cofinite_eq_at_top]
      filterUpwards [h]
      intro n hn 
      byContra h 
      pushNeg  at h 
      exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_ltₓ hn$ mul_neg_of_neg_of_pos hr₀ h)

theorem summable_of_ratio_test_tendsto_lt_one {α : Type _} [NormedGroup α] [CompleteSpace α] {f : ℕ → α} {l : ℝ}
  (hl₁ : l < 1) (hf : ∀ᶠn in at_top, f n ≠ 0) (h : tendsto (fun n => ∥f (n+1)∥ / ∥f n∥) at_top (𝓝 l)) : Summable f :=
  by 
    rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
    refine' summable_of_ratio_norm_eventually_le hr₁ _ 
    filterUpwards [eventually_le_of_tendsto_lt hr₀ h, hf]
    intro n h₀ h₁ 
    rwa [←div_le_iff (norm_pos_iff.mpr h₁)]

theorem not_summable_of_ratio_norm_eventually_ge {α : Type _} [SemiNormedGroup α] {f : ℕ → α} {r : ℝ} (hr : 1 < r)
  (hf : ∃ᶠn in at_top, ∥f n∥ ≠ 0) (h : ∀ᶠn in at_top, (r*∥f n∥) ≤ ∥f (n+1)∥) : ¬Summable f :=
  by 
    rw [eventually_at_top] at h 
    rcases h with ⟨N₀, hN₀⟩
    rw [frequently_at_top] at hf 
    rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
    rw [←@summable_nat_add_iff α _ _ _ _ N]
    refine' mt Summable.tendsto_at_top_zero fun h' => not_tendsto_at_top_of_tendsto_nhds (tendsto_norm_zero.comp h') _ 
    convert tendsto_at_top_of_geom_le _ hr _
    ·
      refine' lt_of_le_of_neₓ (norm_nonneg _) _ 
      intro h'' 
      specialize hN₀ N hNN₀ 
      simp only [comp_app, zero_addₓ] at h'' 
      exact hN h''.symm
    ·
      intro i 
      dsimp only [comp_app]
      convert hN₀ (i+N) (hNN₀.trans (N.le_add_left i)) using 3
      acRfl

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem not_summable_of_ratio_test_tendsto_gt_one
{α : Type*}
[semi_normed_group α]
{f : exprℕ() → α}
{l : exprℝ()}
(hl : «expr < »(1, l))
(h : tendsto (λ
  n, «expr / »(«expr∥ ∥»(f «expr + »(n, 1)), «expr∥ ∥»(f n))) at_top (expr𝓝() l)) : «expr¬ »(summable f) :=
begin
  have [ident key] [":", expr «expr∀ᶠ in , »((n), at_top, «expr ≠ »(«expr∥ ∥»(f n), 0))] [],
  { filter_upwards ["[", expr eventually_ge_of_tendsto_gt hl h, "]"] [],
    intros [ident n, ident hn, ident hc],
    rw ["[", expr hc, ",", expr div_zero, "]"] ["at", ident hn],
    linarith [] [] [] },
  rcases [expr exists_between hl, "with", "⟨", ident r, ",", ident hr₀, ",", ident hr₁, "⟩"],
  refine [expr not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently _],
  filter_upwards ["[", expr eventually_ge_of_tendsto_gt hr₁ h, ",", expr key, "]"] [],
  intros [ident n, ident h₀, ident h₁],
  rwa ["<-", expr le_div_iff (lt_of_le_of_ne (norm_nonneg _) h₁.symm)] []
end

/-- A series whose terms are bounded by the terms of a converging geometric series converges. -/
theorem summable_one_div_pow_of_le {m : ℝ} {f : ℕ → ℕ} (hm : 1 < m) (fi : ∀ i, i ≤ f i) :
  Summable fun i => 1 / m ^ f i :=
  by 
    refine'
      summable_of_nonneg_of_le (fun a => one_div_nonneg.mpr (pow_nonneg (zero_le_one.trans hm.le) _)) (fun a => _)
        (summable_geometric_of_lt_1 (one_div_nonneg.mpr (zero_le_one.trans hm.le))
          ((one_div_lt (zero_lt_one.trans hm) zero_lt_one).mpr (one_div_one.le.trans_lt hm)))
    rw [div_pow, one_pow]
    refine' (one_div_le_one_div _ _).mpr (pow_le_pow hm.le (fi a)) <;> exact pow_pos (zero_lt_one.trans hm) _

/-! ### Positive sequences with small sums on encodable types -/


-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- For any positive `ε`, define on an encodable type a positive sequence with sum less than `ε` -/
def pos_sum_of_encodable
{ε : exprℝ()}
(hε : «expr < »(0, ε))
(ι)
[encodable ι] : {ε' : ι → exprℝ() // «expr ∧ »(∀
 i, «expr < »(0, ε' i), «expr∃ , »((c), «expr ∧ »(has_sum ε' c, «expr ≤ »(c, ε))))} :=
begin
  let [ident f] [] [":=", expr λ n, «expr / »(«expr / »(ε, 2), «expr ^ »(2, n))],
  have [ident hf] [":", expr has_sum f ε] [":=", expr has_sum_geometric_two' _],
  have [ident f0] [":", expr ∀ n, «expr < »(0, f n)] [":=", expr λ n, div_pos (half_pos hε) (pow_pos zero_lt_two _)],
  refine [expr ⟨«expr ∘ »(f, encodable.encode), λ i, f0 _, _⟩],
  rcases [expr hf.summable.comp_injective (@encodable.encode_injective ι _), "with", "⟨", ident c, ",", ident hg, "⟩"],
  refine [expr ⟨c, hg, has_sum_le_inj _ (@encodable.encode_injective ι _) _ _ hg hf⟩],
  { assume [binders (i _)],
    exact [expr le_of_lt (f0 _)] },
  { assume [binders (n)],
    exact [expr le_refl _] }
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem set.countable.exists_pos_has_sum_le
{ι : Type*}
{s : set ι}
(hs : s.countable)
{ε : exprℝ()}
(hε : «expr < »(0, ε)) : «expr∃ , »((ε' : ι → exprℝ()), «expr ∧ »(∀
  i, «expr < »(0, ε' i), «expr∃ , »((c), «expr ∧ »(has_sum (λ i : s, ε' i) c, «expr ≤ »(c, ε))))) :=
begin
  haveI [] [] [":=", expr hs.to_encodable],
  rcases [expr pos_sum_of_encodable hε s, "with", "⟨", ident f, ",", ident hf0, ",", "⟨", ident c, ",", ident hfc, ",", ident hcε, "⟩", "⟩"],
  refine [expr ⟨λ i, if h : «expr ∈ »(i, s) then f ⟨i, h⟩ else 1, λ i, _, ⟨c, _, hcε⟩⟩],
  { split_ifs [] [],
    exacts ["[", expr hf0 _, ",", expr zero_lt_one, "]"] },
  { simpa [] [] ["only"] ["[", expr subtype.coe_prop, ",", expr dif_pos, ",", expr subtype.coe_eta, "]"] [] [] }
end

theorem Set.Countable.exists_pos_forall_sum_le {ι : Type _} {s : Set ι} (hs : s.countable) {ε : ℝ} (hε : 0 < ε) :
  ∃ ε' : ι → ℝ, (∀ i, 0 < ε' i) ∧ ∀ t : Finset ι, «expr↑ » t ⊆ s → (∑i in t, ε' i) ≤ ε :=
  by 
    rcases hs.exists_pos_has_sum_le hε with ⟨ε', hpos, c, hε'c, hcε⟩
    refine' ⟨ε', hpos, fun t ht => _⟩
    rw [←sum_subtype_of_mem _ ht]
    refine' (sum_le_has_sum _ _ hε'c).trans hcε 
    exact fun _ _ => (hpos _).le

namespace Nnreal

theorem exists_pos_sum_of_encodable {ε :  ℝ≥0 } (hε : ε ≠ 0) ι [Encodable ι] :
  ∃ ε' : ι →  ℝ≥0 , (∀ i, 0 < ε' i) ∧ ∃ c, HasSum ε' c ∧ c < ε :=
  let ⟨a, a0, aε⟩ := exists_between (pos_iff_ne_zero.2 hε)
  let ⟨ε', hε', c, hc, hcε⟩ := posSumOfEncodable a0 ι
  ⟨fun i => ⟨ε' i, le_of_ltₓ$ hε' i⟩, fun i => Nnreal.coe_lt_coe.1$ hε' i,
    ⟨c, has_sum_le (fun i => le_of_ltₓ$ hε' i) has_sum_zero hc⟩, Nnreal.has_sum_coe.1 hc,
    lt_of_le_of_ltₓ (Nnreal.coe_le_coe.1 hcε) aε⟩

end Nnreal

namespace Ennreal

theorem exists_pos_sum_of_encodable {ε : ℝ≥0∞} (hε : ε ≠ 0) ι [Encodable ι] :
  ∃ ε' : ι →  ℝ≥0 , (∀ i, 0 < ε' i) ∧ (∑'i, (ε' i : ℝ≥0∞)) < ε :=
  by 
    rcases exists_between (pos_iff_ne_zero.2 hε) with ⟨r, h0r, hrε⟩
    rcases lt_iff_exists_coe.1 hrε with ⟨x, rfl, hx⟩
    rcases Nnreal.exists_pos_sum_of_encodable (coe_pos.1 h0r).ne' ι with ⟨ε', hp, c, hc, hcr⟩
    exact ⟨ε', hp, (Ennreal.tsum_coe_eq hc).symm ▸ lt_transₓ (coe_lt_coe.2 hcr) hrε⟩

theorem exists_pos_sum_of_encodable' {ε : ℝ≥0∞} (hε : ε ≠ 0) ι [Encodable ι] :
  ∃ ε' : ι → ℝ≥0∞, (∀ i, 0 < ε' i) ∧ (∑'i, ε' i) < ε :=
  let ⟨δ, δpos, hδ⟩ := exists_pos_sum_of_encodable hε ι
  ⟨fun i => δ i, fun i => Ennreal.coe_pos.2 (δpos i), hδ⟩

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem exists_pos_tsum_mul_lt_of_encodable
{ε : «exprℝ≥0∞»()}
(hε : «expr ≠ »(ε, 0))
{ι}
[encodable ι]
(w : ι → «exprℝ≥0∞»())
(hw : ∀
 i, «expr ≠ »(w i, «expr∞»())) : «expr∃ , »((δ : ι → «exprℝ≥0»()), «expr ∧ »(∀
  i, «expr < »(0, δ i), «expr < »(«expr∑' , »((i), («expr * »(w i, δ i) : «exprℝ≥0∞»())), ε))) :=
begin
  lift [expr w] ["to", expr ι → «exprℝ≥0»()] ["using", expr hw] [],
  rcases [expr exists_pos_sum_of_encodable hε ι, "with", "⟨", ident δ', ",", ident Hpos, ",", ident Hsum, "⟩"],
  have [] [":", expr ∀ i, «expr < »(0, max 1 (w i))] [],
  from [expr λ i, zero_lt_one.trans_le (le_max_left _ _)],
  refine [expr ⟨λ i, «expr / »(δ' i, max 1 (w i)), λ i, nnreal.div_pos (Hpos _) (this i), _⟩],
  refine [expr lt_of_le_of_lt «expr $ »(ennreal.tsum_le_tsum, λ i, _) Hsum],
  rw ["[", expr coe_div (this i).ne', "]"] [],
  refine [expr mul_le_of_le_div' «expr $ »(ennreal.mul_le_mul le_rfl, ennreal.inv_le_inv.2 _)],
  exact [expr coe_le_coe.2 (le_max_right _ _)]
end

end Ennreal

/-!
### Factorial
-/


theorem factorial_tendsto_at_top : tendsto Nat.factorial at_top at_top :=
  tendsto_at_top_at_top_of_monotone Nat.monotone_factorial fun n => ⟨n, n.self_le_factorial⟩

theorem tendsto_factorial_div_pow_self_at_top : tendsto (fun n => n ! / n ^ n : ℕ → ℝ) at_top (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (tendsto_const_div_at_top_nhds_0_nat 1)
    (eventually_of_forall$
      fun n =>
        div_nonneg
          (by 
            exactModCast n.factorial_pos.le)
          (pow_nonneg
            (by 
              exactModCast n.zero_le)
            _))
    (by 
      refine' (eventually_gt_at_top 0).mono fun n hn => _ 
      rcases Nat.exists_eq_succ_of_ne_zero hn.ne.symm with ⟨k, rfl⟩
      rw [←prod_range_add_one_eq_factorial, pow_eq_prod_const, div_eq_mul_inv, ←inv_eq_one_div, prod_nat_cast,
        Nat.cast_succ, ←prod_inv_distrib', ←prod_mul_distrib, Finset.prod_range_succ']
      simp only [prod_range_succ', one_mulₓ, Nat.cast_add, zero_addₓ, Nat.cast_one]
      refine'
          mul_le_of_le_one_left
            (inv_nonneg.mpr$
              by 
                exactModCast hn.le)
            (prod_le_one _ _) <;>
        intro x hx <;> rw [Finset.mem_range] at hx
      ·
        refine' mul_nonneg _ (inv_nonneg.mpr _) <;> normCast <;> linarith
      ·
        refine'
          (div_le_one$
                by 
                  exactModCast hn).mpr
            _ 
        normCast 
        linarith)

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `exp_series_field_summable`
for a version that also works in `ℂ`, and `exp_series_summable'` for a version that works in
any normed algebra over `ℝ` or `ℂ`. -/
theorem real.summable_pow_div_factorial
(x : exprℝ()) : summable (λ n, «expr / »(«expr ^ »(x, n), «expr !»(n)) : exprℕ() → exprℝ()) :=
begin
  have [ident A] [":", expr «expr < »((0 : exprℝ()), «expr + »(«expr⌊ ⌋₊»(«expr∥ ∥»(x)), 1))] [],
  from [expr zero_lt_one.trans_le (by simp [] [] [] [] [] [])],
  have [ident B] [":", expr «expr < »(«expr / »(«expr∥ ∥»(x), «expr + »(«expr⌊ ⌋₊»(«expr∥ ∥»(x)), 1)), 1)] [],
  from [expr (div_lt_one A).2 (nat.lt_floor_add_one _)],
  suffices [] [":", expr ∀
   n «expr ≥ » «expr⌊ ⌋₊»(«expr∥ ∥»(x)), «expr ≤ »(«expr∥ ∥»(«expr / »(«expr ^ »(x, «expr + »(n, 1)), «expr !»(«expr + »(n, 1)))), «expr * »(«expr / »(«expr∥ ∥»(x), «expr + »(«expr⌊ ⌋₊»(«expr∥ ∥»(x)), 1)), «expr∥ ∥»(«expr / »(«expr ^ »(x, n), «expr↑ »(«expr !»(n))))))],
  from [expr summable_of_ratio_norm_eventually_le B (eventually_at_top.2 ⟨«expr⌊ ⌋₊»(«expr∥ ∥»(x)), this⟩)],
  intros [ident n, ident hn],
  calc
    «expr = »(«expr∥ ∥»(«expr / »(«expr ^ »(x, «expr + »(n, 1)), «expr !»(«expr + »(n, 1)))), «expr * »(«expr / »(«expr∥ ∥»(x), «expr + »(n, 1)), «expr∥ ∥»(«expr / »(«expr ^ »(x, n), «expr !»(n))))) : by rw ["[", expr pow_succ, ",", expr nat.factorial_succ, ",", expr nat.cast_mul, ",", "<-", expr div_mul_div, ",", expr normed_field.norm_mul, ",", expr normed_field.norm_div, ",", expr real.norm_coe_nat, ",", expr nat.cast_succ, "]"] []
    «expr ≤ »(..., «expr * »(«expr / »(«expr∥ ∥»(x), «expr + »(«expr⌊ ⌋₊»(«expr∥ ∥»(x)), 1)), «expr∥ ∥»(«expr / »(«expr ^ »(x, n), «expr !»(n))))) : by mono ["*"] [] ["with", "[", expr «expr ≤ »(0, «expr∥ ∥»(«expr / »(«expr ^ »(x, n), «expr !»(n)))), ",", expr «expr ≤ »(0, «expr∥ ∥»(x)), "]"] []; apply [expr norm_nonneg]
end

theorem Real.tendsto_pow_div_factorial_at_top (x : ℝ) : tendsto (fun n => x ^ n / n ! : ℕ → ℝ) at_top (𝓝 0) :=
  (Real.summable_pow_div_factorial x).tendsto_at_top_zero

/-!
### Ceil and floor
-/


section 

variable{R : Type _}[TopologicalSpace R][LinearOrderedField R][OrderTopology R][FloorRing R]

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_nat_floor_mul_div_at_top
{a : R}
(ha : «expr ≤ »(0, a)) : tendsto (λ x, «expr / »((«expr⌊ ⌋₊»(«expr * »(a, x)) : R), x)) at_top (expr𝓝() a) :=
begin
  have [ident A] [":", expr tendsto (λ
    x : R, «expr - »(a, «expr ⁻¹»(x))) at_top (expr𝓝() «expr - »(a, 0))] [":=", expr tendsto_const_nhds.sub tendsto_inv_at_top_zero],
  rw [expr sub_zero] ["at", ident A],
  apply [expr tendsto_of_tendsto_of_tendsto_of_le_of_le' A tendsto_const_nhds],
  { refine [expr eventually_at_top.2 ⟨1, λ x hx, _⟩],
    simp [] [] ["only"] ["[", expr le_div_iff (zero_lt_one.trans_le hx), ",", expr sub_mul, ",", expr inv_mul_cancel (zero_lt_one.trans_le hx).ne', "]"] [] [],
    have [] [] [":=", expr nat.lt_floor_add_one «expr * »(a, x)],
    linarith [] [] [] },
  { refine [expr eventually_at_top.2 ⟨1, λ x hx, _⟩],
    rw [expr div_le_iff (zero_lt_one.trans_le hx)] [],
    simp [] [] [] ["[", expr nat.floor_le (mul_nonneg ha (zero_le_one.trans hx)), "]"] [] [] }
end

-- error in Analysis.SpecificLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem tendsto_nat_ceil_mul_div_at_top
{a : R}
(ha : «expr ≤ »(0, a)) : tendsto (λ x, «expr / »((«expr⌈ ⌉₊»(«expr * »(a, x)) : R), x)) at_top (expr𝓝() a) :=
begin
  have [ident A] [":", expr tendsto (λ
    x : R, «expr + »(a, «expr ⁻¹»(x))) at_top (expr𝓝() «expr + »(a, 0))] [":=", expr tendsto_const_nhds.add tendsto_inv_at_top_zero],
  rw [expr add_zero] ["at", ident A],
  apply [expr tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds A],
  { refine [expr eventually_at_top.2 ⟨1, λ x hx, _⟩],
    rw [expr le_div_iff (zero_lt_one.trans_le hx)] [],
    exact [expr nat.le_ceil _] },
  { refine [expr eventually_at_top.2 ⟨1, λ x hx, _⟩],
    simp [] [] [] ["[", expr div_le_iff (zero_lt_one.trans_le hx), ",", expr inv_mul_cancel (zero_lt_one.trans_le hx).ne', ",", expr (nat.ceil_lt_add_one (mul_nonneg ha (zero_le_one.trans hx))).le, ",", expr add_mul, "]"] [] [] }
end

end 

