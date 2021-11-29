import Mathbin.Analysis.SpecialFunctions.Pow

/-!
# Convergence of `p`-series

In this file we prove that the series `∑' k in ℕ, 1 / k ^ p` converges if and only if `p > 1`.
The proof is based on the
[Cauchy condensation test](https://en.wikipedia.org/wiki/Cauchy_condensation_test): `∑ k, f k`
converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. We prove this test in
`nnreal.summable_condensed_iff` and `summable_condensed_iff_of_nonneg`, then use it to prove
`summable_one_div_rpow`. After this transformation, a `p`-series turns into a geometric series.

## TODO

It should be easy to generalize arguments to Schlömilch's generalization of the Cauchy condensation
test once we need it.

## Tags

p-series, Cauchy condensation test
-/


open Filter

open_locale BigOperators Ennreal Nnreal TopologicalSpace

/-!
### Cauchy condensation test

In this section we prove the Cauchy condensation test: for `f : ℕ → ℝ≥0` or `f : ℕ → ℝ`,
`∑ k, f k` converges if and only if so does `∑ k, 2 ^ k f (2 ^ k)`. Instead of giving a monolithic
proof, we split it into a series of lemmas with explicit estimates of partial sums of each series in
terms of the partial sums of the other series.
-/


namespace Finset

variable {M : Type _} [OrderedAddCommMonoid M] {f : ℕ → M}

-- error in Analysis.PSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem le_sum_condensed'
(hf : ∀ {{m n}}, «expr < »(0, m) → «expr ≤ »(m, n) → «expr ≤ »(f n, f m))
(n : exprℕ()) : «expr ≤ »(«expr∑ in , »((k), Ico 1 «expr ^ »(2, n), f k), «expr∑ in , »((k), range n, «expr • »(«expr ^ »(2, k), f «expr ^ »(2, k)))) :=
begin
  induction [expr n] [] ["with", ident n, ident ihn] [],
  { simp [] [] [] [] [] [] },
  suffices [] [":", expr «expr ≤ »(«expr∑ in , »((k), Ico «expr ^ »(2, n) «expr ^ »(2, «expr + »(n, 1)), f k), «expr • »(«expr ^ »(2, n), f «expr ^ »(2, n)))],
  { rw ["[", expr sum_range_succ, ",", "<-", expr sum_Ico_consecutive, "]"] [],
    exact [expr add_le_add ihn this],
    exacts ["[", expr n.one_le_two_pow, ",", expr nat.pow_le_pow_of_le_right zero_lt_two n.le_succ, "]"] },
  have [] [":", expr ∀
   k «expr ∈ » Ico «expr ^ »(2, n) «expr ^ »(2, «expr + »(n, 1)), «expr ≤ »(f k, f «expr ^ »(2, n))] [":=", expr λ
   k hk, hf (pow_pos zero_lt_two _) (mem_Ico.mp hk).1],
  convert [] [expr sum_le_sum this] [],
  simp [] [] [] ["[", expr pow_succ, ",", expr two_mul, "]"] [] []
end

theorem le_sum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑k in range (2^n), f k) ≤ f 0+∑k in range n, (2^k) • f (2^k) :=
  by 
    convert add_le_add_left (le_sum_condensed' hf n) (f 0)
    rw [←sum_range_add_sum_Ico _ n.one_le_two_pow, sum_range_succ, sum_range_zero, zero_addₓ]

-- error in Analysis.PSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem sum_condensed_le'
(hf : ∀ {{m n}}, «expr < »(1, m) → «expr ≤ »(m, n) → «expr ≤ »(f n, f m))
(n : exprℕ()) : «expr ≤ »(«expr∑ in , »((k), range n, «expr • »(«expr ^ »(2, k), f «expr ^ »(2, «expr + »(k, 1)))), «expr∑ in , »((k), Ico 2 «expr + »(«expr ^ »(2, n), 1), f k)) :=
begin
  induction [expr n] [] ["with", ident n, ident ihn] [],
  { simp [] [] [] [] [] [] },
  suffices [] [":", expr «expr ≤ »(«expr • »(«expr ^ »(2, n), f «expr ^ »(2, «expr + »(n, 1))), «expr∑ in , »((k), Ico «expr + »(«expr ^ »(2, n), 1) «expr + »(«expr ^ »(2, «expr + »(n, 1)), 1), f k))],
  { rw ["[", expr sum_range_succ, ",", "<-", expr sum_Ico_consecutive, "]"] [],
    exact [expr add_le_add ihn this],
    exacts ["[", expr add_le_add_right n.one_le_two_pow _, ",", expr add_le_add_right (nat.pow_le_pow_of_le_right zero_lt_two n.le_succ) _, "]"] },
  have [] [":", expr ∀
   k «expr ∈ » Ico «expr + »(«expr ^ »(2, n), 1) «expr + »(«expr ^ »(2, «expr + »(n, 1)), 1), «expr ≤ »(f «expr ^ »(2, «expr + »(n, 1)), f k)] [":=", expr λ
   k
   hk, hf «expr $ »(n.one_le_two_pow.trans_lt, (nat.lt_succ_of_le le_rfl).trans_le (mem_Ico.mp hk).1) «expr $ »(nat.le_of_lt_succ, (mem_Ico.mp hk).2)],
  convert [] [expr sum_le_sum this] [],
  simp [] [] [] ["[", expr pow_succ, ",", expr two_mul, "]"] [] []
end

theorem sum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) (n : ℕ) :
  (∑k in range (n+1), (2^k) • f (2^k)) ≤ f 1+2 • ∑k in Ico 2 ((2^n)+1), f k :=
  by 
    convert add_le_add_left (nsmul_le_nsmul_of_le_right (sum_condensed_le' hf n) 2) (f 1)
    simp [sum_range_succ', add_commₓ, pow_succₓ, mul_nsmul, sum_nsmul]

end Finset

namespace Ennreal

variable {f : ℕ → ℝ≥0∞}

theorem le_tsum_condensed (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) : (∑'k, f k) ≤ f 0+∑'k : ℕ, (2^k)*f (2^k) :=
  by 
    rw [Ennreal.tsum_eq_supr_nat' (Nat.tendsto_pow_at_top_at_top_of_one_lt _root_.one_lt_two)]
    refine' supr_le fun n => (Finset.le_sum_condensed hf n).trans (add_le_add_left _ _)
    simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_two]
    apply Ennreal.sum_le_tsum

theorem tsum_condensed_le (hf : ∀ ⦃m n⦄, 1 < m → m ≤ n → f n ≤ f m) : (∑'k : ℕ, (2^k)*f (2^k)) ≤ f 1+2*∑'k, f k :=
  by 
    rw [Ennreal.tsum_eq_supr_nat' (tendsto_at_top_mono Nat.le_succₓ tendsto_id), two_mul, ←two_nsmul]
    refine'
      supr_le
        fun n =>
          le_transₓ _ (add_le_add_left (nsmul_le_nsmul_of_le_right (Ennreal.sum_le_tsum$ Finset.ico 2 ((2^n)+1)) _) _)
    simpa using Finset.sum_condensed_le hf n

end Ennreal

namespace Nnreal

/-- Cauchy condensation test for a series of `nnreal` version. -/
theorem summable_condensed_iff {f : ℕ →  ℝ≥0 } (hf : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) :
  (Summable fun k : ℕ => (2^k)*f (2^k)) ↔ Summable f :=
  by 
    simp only [←Ennreal.tsum_coe_ne_top_iff_summable, Ne.def, not_iff_not, Ennreal.coe_mul, Ennreal.coe_pow,
      Ennreal.coe_two]
    split  <;> intro h
    ·
      replace hf : ∀ m n, 1 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m :=
        fun m n hm hmn => Ennreal.coe_le_coe.2 (hf (zero_lt_one.trans hm) hmn)
      simpa [h, Ennreal.add_eq_top] using Ennreal.tsum_condensed_le hf
    ·
      replace hf : ∀ m n, 0 < m → m ≤ n → (f n : ℝ≥0∞) ≤ f m := fun m n hm hmn => Ennreal.coe_le_coe.2 (hf hm hmn)
      simpa [h, Ennreal.add_eq_top] using Ennreal.le_tsum_condensed hf

end Nnreal

/-- Cauchy condensation test for series of nonnegative real numbers. -/
theorem summable_condensed_iff_of_nonneg {f : ℕ → ℝ} (h_nonneg : ∀ n, 0 ≤ f n)
  (h_mono : ∀ ⦃m n⦄, 0 < m → m ≤ n → f n ≤ f m) : (Summable fun k : ℕ => (2^k)*f (2^k)) ↔ Summable f :=
  by 
    lift f to ℕ →  ℝ≥0  using h_nonneg 
    simp only [Nnreal.coe_le_coe] at *
    exactModCast Nnreal.summable_condensed_iff h_mono

open Real

/-!
### Convergence of the `p`-series

In this section we prove that for a real number `p`, the series `∑' n : ℕ, 1 / (n ^ p)` converges if
and only if `1 < p`. There are many different proofs of this fact. The proof in this file uses the
Cauchy condensation test we formalized above. This test implies that `∑ n, 1 / (n ^ p)` converges if
and only if `∑ n, 2 ^ n / ((2 ^ n) ^ p)` converges, and the latter series is a geometric series with
common ratio `2 ^ {1 - p}`. -/


-- error in Analysis.PSeries: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem real.summable_nat_rpow_inv
{p : exprℝ()} : «expr ↔ »(summable (λ n, «expr ⁻¹»(«expr ^ »(n, p)) : exprℕ() → exprℝ()), «expr < »(1, p)) :=
begin
  cases [expr le_or_lt 0 p] ["with", ident hp, ident hp],
  { rw ["<-", expr summable_condensed_iff_of_nonneg] [],
    { simp_rw ["[", expr nat.cast_pow, ",", expr nat.cast_two, ",", "<-", expr rpow_nat_cast, ",", "<-", expr rpow_mul zero_lt_two.le, ",", expr mul_comm _ p, ",", expr rpow_mul zero_lt_two.le, ",", expr rpow_nat_cast, ",", "<-", expr inv_pow₀, ",", "<-", expr mul_pow, ",", expr summable_geometric_iff_norm_lt_1, "]"] [],
      nth_rewrite [0] ["[", "<-", expr rpow_one 2, "]"] [],
      rw ["[", "<-", expr division_def, ",", "<-", expr rpow_sub zero_lt_two, ",", expr norm_eq_abs, ",", expr abs_of_pos (rpow_pos_of_pos zero_lt_two _), ",", expr rpow_lt_one_iff zero_lt_two.le, "]"] [],
      norm_num [] [] },
    { intro [ident n],
      exact [expr inv_nonneg.2 (rpow_nonneg_of_nonneg n.cast_nonneg _)] },
    { intros [ident m, ident n, ident hm, ident hmn],
      exact [expr inv_le_inv_of_le (rpow_pos_of_pos (nat.cast_pos.2 hm) _) (rpow_le_rpow m.cast_nonneg (nat.cast_le.2 hmn) hp)] } },
  { suffices [] [":", expr «expr¬ »(summable (λ n, «expr ⁻¹»(«expr ^ »(n, p)) : exprℕ() → exprℝ()))],
    { have [] [":", expr «expr¬ »(«expr < »(1, p))] [":=", expr λ hp₁, hp.not_le (zero_le_one.trans hp₁.le)],
      simpa [] [] [] ["[", expr this, ",", "-", ident one_div, "]"] [] [] },
    { intro [ident h],
      obtain ["⟨", ident k, ":", expr exprℕ(), ",", ident hk₁, ":", expr «expr < »((«expr ⁻¹»(«expr ^ »(k, p)) : exprℝ()), 1), ",", ident hk₀, ":", expr «expr ≠ »(k, 0), "⟩", ":=", expr ((h.tendsto_cofinite_zero.eventually (gt_mem_nhds zero_lt_one)).and (eventually_cofinite_ne 0)).exists],
      apply [expr hk₀],
      rw ["[", "<-", expr pos_iff_ne_zero, ",", "<-", expr @nat.cast_pos exprℝ(), "]"] ["at", ident hk₀],
      simpa [] [] [] ["[", expr inv_lt_one_iff_of_pos (rpow_pos_of_pos hk₀ _), ",", expr one_lt_rpow_iff_of_pos hk₀, ",", expr hp, ",", expr hp.not_lt, ",", expr hk₀, "]"] [] ["using", expr hk₁] } }
end

@[simp]
theorem Real.summable_nat_rpow {p : ℝ} : Summable (fun n => n^p : ℕ → ℝ) ↔ p < -1 :=
  by 
    rcases neg_surjective p with ⟨p, rfl⟩
    simp [rpow_neg]

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_rpow {p : ℝ} : Summable (fun n => 1 / (n^p) : ℕ → ℝ) ↔ 1 < p :=
  by 
    simp 

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, (n ^ p)⁻¹` converges
if and only if `1 < p`. -/
@[simp]
theorem Real.summable_nat_pow_inv {p : ℕ} : Summable (fun n => (n^p)⁻¹ : ℕ → ℝ) ↔ 1 < p :=
  by 
    simp only [←rpow_nat_cast, Real.summable_nat_rpow_inv, Nat.one_lt_cast]

/-- Test for convergence of the `p`-series: the real-valued series `∑' n : ℕ, 1 / n ^ p` converges
if and only if `1 < p`. -/
theorem Real.summable_one_div_nat_pow {p : ℕ} : Summable (fun n => 1 / (n^p) : ℕ → ℝ) ↔ 1 < p :=
  by 
    simp 

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_nat_cast_inv : ¬Summable (fun n => n⁻¹ : ℕ → ℝ) :=
  have  : ¬Summable (fun n => (n^1)⁻¹ : ℕ → ℝ) := mt Real.summable_nat_pow_inv.1 (lt_irreflₓ 1)
  by 
    simpa

/-- Harmonic series is not unconditionally summable. -/
theorem Real.not_summable_one_div_nat_cast : ¬Summable (fun n => 1 / n : ℕ → ℝ) :=
  by 
    simpa only [inv_eq_one_div] using Real.not_summable_nat_cast_inv

/-- **Divergence of the Harmonic Series** -/
theorem Real.tendsto_sum_range_one_div_nat_succ_at_top :
  tendsto (fun n => ∑i in Finset.range n, (1 / i+1 : ℝ)) at_top at_top :=
  by 
    rw [←not_summable_iff_tendsto_nat_at_top_of_nonneg]
    ·
      exactModCast mt (summable_nat_add_iff 1).1 Real.not_summable_one_div_nat_cast
    ·
      exact fun i => div_nonneg zero_le_one i.cast_add_one_pos.le

@[simp]
theorem Nnreal.summable_rpow_inv {p : ℝ} : Summable (fun n => (n^p)⁻¹ : ℕ →  ℝ≥0 ) ↔ 1 < p :=
  by 
    simp [←Nnreal.summable_coe]

@[simp]
theorem Nnreal.summable_rpow {p : ℝ} : Summable (fun n => n^p : ℕ →  ℝ≥0 ) ↔ p < -1 :=
  by 
    simp [←Nnreal.summable_coe]

theorem Nnreal.summable_one_div_rpow {p : ℝ} : Summable (fun n => 1 / (n^p) : ℕ →  ℝ≥0 ) ↔ 1 < p :=
  by 
    simp 

