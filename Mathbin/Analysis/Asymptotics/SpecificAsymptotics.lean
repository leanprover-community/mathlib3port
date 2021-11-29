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

variable{𝕜 : Type _}[LinearOrderedField 𝕜]

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pow_div_pow_eventually_eq_at_top
{p
 q : exprℕ()} : «expr =ᶠ[ ] »(λ
 x : 𝕜, «expr / »(«expr ^ »(x, p), «expr ^ »(x, q)), at_top, λ x, «expr ^ »(x, «expr - »((p : exprℤ()), q))) :=
begin
  apply [expr (eventually_gt_at_top (0 : 𝕜)).mono (λ x hx, _)],
  simp [] [] [] ["[", expr zpow_sub₀ hx.ne', "]"] [] []
end

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem pow_div_pow_eventually_eq_at_bot
{p
 q : exprℕ()} : «expr =ᶠ[ ] »(λ
 x : 𝕜, «expr / »(«expr ^ »(x, p), «expr ^ »(x, q)), at_bot, λ x, «expr ^ »(x, «expr - »((p : exprℤ()), q))) :=
begin
  apply [expr (eventually_lt_at_bot (0 : 𝕜)).mono (λ x hx, _)],
  simp [] [] [] ["[", expr zpow_sub₀ hx.ne'.symm, "]"] [] []
end

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_zpow_at_top_at_top
{n : exprℤ()}
(hn : «expr < »(0, n)) : tendsto (λ x : 𝕜, «expr ^ »(x, n)) at_top at_top :=
begin
  lift [expr n] ["to", expr exprℕ()] ["using", expr hn.le] [],
  simp [] [] ["only"] ["[", expr zpow_coe_nat, "]"] [] [],
  exact [expr tendsto_pow_at_top «expr $ »(nat.succ_le_iff.mpr, int.coe_nat_pos.mp hn)]
end

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_pow_div_pow_at_top_at_top
{p q : exprℕ()}
(hpq : «expr < »(q, p)) : tendsto (λ x : 𝕜, «expr / »(«expr ^ »(x, p), «expr ^ »(x, q))) at_top at_top :=
begin
  rw [expr tendsto_congr' pow_div_pow_eventually_eq_at_top] [],
  apply [expr tendsto_zpow_at_top_at_top],
  linarith [] [] []
end

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem tendsto_pow_div_pow_at_top_zero
[topological_space 𝕜]
[order_topology 𝕜]
{p q : exprℕ()}
(hpq : «expr < »(p, q)) : tendsto (λ x : 𝕜, «expr / »(«expr ^ »(x, p), «expr ^ »(x, q))) at_top (expr𝓝() 0) :=
begin
  rw [expr tendsto_congr' pow_div_pow_eventually_eq_at_top] [],
  apply [expr tendsto_zpow_at_top_zero],
  linarith [] [] []
end

end LinearOrderedField

section NormedLinearOrderedField

variable{𝕜 : Type _}[NormedLinearOrderedField 𝕜]

-- error in Analysis.Asymptotics.SpecificAsymptotics: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Parser.Term.explicitBinder'
theorem asymptotics.is_o_pow_pow_at_top_of_lt
[order_topology 𝕜]
{p q : exprℕ()}
(hpq : «expr < »(p, q)) : is_o (λ x : 𝕜, «expr ^ »(x, p)) (λ x, «expr ^ »(x, q)) at_top :=
begin
  refine [expr (is_o_iff_tendsto' _).mpr (tendsto_pow_div_pow_at_top_zero hpq)],
  exact [expr (eventually_gt_at_top 0).mono (λ x hx hxq, (pow_ne_zero q hx.ne' hxq).elim)]
end

theorem Asymptotics.IsO.trans_tendsto_norm_at_top {α : Type _} {u v : α → 𝕜} {l : Filter α} (huv : is_O u v l)
  (hu : tendsto (fun x => ∥u x∥) l at_top) : tendsto (fun x => ∥v x∥) l at_top :=
  by 
    rcases huv.exists_pos with ⟨c, hc, hcuv⟩
    rw [is_O_with] at hcuv 
    convert tendsto.at_top_div_const hc (tendsto_at_top_mono' l hcuv hu)
    ext x 
    rw [mul_div_cancel_left _ hc.ne.symm]

end NormedLinearOrderedField

