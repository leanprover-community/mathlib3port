import Mathbin.Topology.Instances.Real 
import Mathbin.Order.Filter.Archimedean

/-!
# Convergence of subadditive sequences

A subadditive sequence `u : ℕ → ℝ` is a sequence satisfying `u (m + n) ≤ u m + u n` for all `m, n`.
We define this notion as `subadditive u`, and prove in `subadditive.tendsto_lim` that, if `u n / n`
is bounded below, then it converges to a limit (that we denote by `subadditive.lim` for
convenience). This result is known as Fekete's lemma in the literature.
-/


noncomputable theory

open Set Filter

open_locale TopologicalSpace

/-- A real-valued sequence is subadditive if it satisfies the inequality `u (m + n) ≤ u m + u n`
for all `m, n`. -/
def Subadditive (u : ℕ → ℝ) : Prop :=
  ∀ m n, u (m+n) ≤ u m+u n

namespace Subadditive

variable {u : ℕ → ℝ} (h : Subadditive u)

include h

/-- The limit of a bounded-below subadditive sequence. The fact that the sequence indeed tends to
this limit is given in `subadditive.tendsto_lim` -/
@[nolint unused_arguments]
protected irreducible_def limₓ :=
  Inf ((fun n : ℕ => u n / n) '' Ici 1)

theorem lim_le_div (hbdd : BddBelow (range fun n => u n / n)) {n : ℕ} (hn : n ≠ 0) : h.lim ≤ u n / n :=
  by 
    rw [Subadditive.lim]
    apply cInf_le _ _
    ·
      rcases hbdd with ⟨c, hc⟩
      exact ⟨c, fun x hx => hc (image_subset_range _ _ hx)⟩
    ·
      apply mem_image_of_mem 
      exact zero_lt_iff.2 hn

theorem apply_mul_add_le k n r : u ((k*n)+r) ≤ (k*u n)+u r :=
  by 
    induction' k with k IH
    ·
      simp only [Nat.cast_zero, zero_mul, zero_addₓ]
    calc u (((k+1)*n)+r) = u (n+(k*n)+r) :=
      by 
        congr 1
        ring _ ≤ u n+u ((k*n)+r) :=
      h _ _ _ ≤ u n+(k*u n)+u r := add_le_add_left IH _ _ = ((k+1)*u n)+u r :=
      by 
        ring

-- error in Analysis.Subadditive: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem eventually_div_lt_of_div_lt
{L : exprℝ()}
{n : exprℕ()}
(hn : «expr ≠ »(n, 0))
(hL : «expr < »(«expr / »(u n, n), L)) : «expr∀ᶠ in , »((p), at_top, «expr < »(«expr / »(u p, p), L)) :=
begin
  have [ident I] [":", expr ∀ i : exprℕ(), «expr < »(0, i) → «expr ≠ »((i : exprℝ()), 0)] [],
  { assume [binders (i hi)],
    simp [] [] ["only"] ["[", expr hi.ne', ",", expr ne.def, ",", expr nat.cast_eq_zero, ",", expr not_false_iff, "]"] [] [] },
  obtain ["⟨", ident w, ",", ident nw, ",", ident wL, "⟩", ":", expr «expr∃ , »((w), «expr ∧ »(«expr < »(«expr / »(u n, n), w), «expr < »(w, L))), ":=", expr exists_between hL],
  obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr «expr∃ , »((x), ∀
    i «expr < » n, «expr ≤ »(«expr - »(u i, «expr * »(i, w)), x))],
  { obtain ["⟨", ident x, ",", ident hx, "⟩", ":", expr bdd_above «expr↑ »(finset.image (λ
       i, «expr - »(u i, «expr * »(i, w))) (finset.range n)), ":=", expr finset.bdd_above _],
    refine [expr ⟨x, λ i hi, _⟩],
    simp [] [] ["only"] ["[", expr upper_bounds, ",", expr mem_image, ",", expr and_imp, ",", expr forall_exists_index, ",", expr mem_set_of_eq, ",", expr forall_apply_eq_imp_iff₂, ",", expr finset.mem_range, ",", expr finset.mem_coe, ",", expr finset.coe_image, "]"] [] ["at", ident hx],
    exact [expr hx _ hi] },
  have [ident A] [":", expr ∀ p : exprℕ(), «expr ≤ »(u p, «expr + »(«expr * »(p, w), x))] [],
  { assume [binders (p)],
    let [ident s] [] [":=", expr «expr / »(p, n)],
    let [ident r] [] [":=", expr «expr % »(p, n)],
    have [ident hp] [":", expr «expr = »(p, «expr + »(«expr * »(s, n), r))] [],
    by rw ["[", expr mul_comm, ",", expr nat.div_add_mod, "]"] [],
    calc
      «expr = »(u p, u «expr + »(«expr * »(s, n), r)) : by rw [expr hp] []
      «expr ≤ »(..., «expr + »(«expr * »(s, u n), u r)) : h.apply_mul_add_le _ _ _
      «expr = »(..., «expr + »(«expr * »(«expr * »(s, n), «expr / »(u n, n)), u r)) : by { field_simp [] ["[", expr I _ hn.bot_lt, "]"] [] [],
        ring [] }
      «expr ≤ »(..., «expr + »(«expr * »(«expr * »(s, n), w), u r)) : add_le_add_right (mul_le_mul_of_nonneg_left nw.le (mul_nonneg (nat.cast_nonneg _) (nat.cast_nonneg _))) _
      «expr = »(..., «expr + »(«expr * »(«expr + »(«expr * »(s, n), r), w), «expr - »(u r, «expr * »(r, w)))) : by ring []
      «expr = »(..., «expr + »(«expr * »(p, w), «expr - »(u r, «expr * »(r, w)))) : by { rw [expr hp] [],
        simp [] [] ["only"] ["[", expr nat.cast_add, ",", expr nat.cast_mul, "]"] [] [] }
      «expr ≤ »(..., «expr + »(«expr * »(p, w), x)) : add_le_add_left (hx _ (nat.mod_lt _ hn.bot_lt)) _ },
  have [ident B] [":", expr «expr∀ᶠ in , »((p), at_top, «expr ≤ »(«expr / »(u p, p), «expr + »(w, «expr / »(x, p))))] [],
  { refine [expr eventually_at_top.2 ⟨1, λ p hp, _⟩],
    simp [] [] ["only"] ["[", expr I p hp, ",", expr ne.def, ",", expr not_false_iff, "]"] ["with", ident field_simps] [],
    refine [expr div_le_div_of_le_of_nonneg _ (nat.cast_nonneg _)],
    rw [expr mul_comm] [],
    exact [expr A _] },
  have [ident C] [":", expr «expr∀ᶠ in , »((p : exprℕ()), at_top, «expr < »(«expr + »(w, «expr / »(x, p)), L))] [],
  { have [] [":", expr tendsto (λ
      p : exprℕ(), «expr + »(w, «expr / »(x, p))) at_top (expr𝓝() «expr + »(w, 0))] [":=", expr tendsto_const_nhds.add (tendsto_const_nhds.div_at_top tendsto_coe_nat_at_top_at_top)],
    rw [expr add_zero] ["at", ident this],
    exact [expr (tendsto_order.1 this).2 _ wL] },
  filter_upwards ["[", expr B, ",", expr C, "]"] [],
  assume [binders (p hp h'p)],
  exact [expr hp.trans_lt h'p]
end

/-- Fekete's lemma: a subadditive sequence which is bounded below converges. -/
theorem tendsto_lim (hbdd : BddBelow (range fun n => u n / n)) : tendsto (fun n => u n / n) at_top (𝓝 h.lim) :=
  by 
    refine' tendsto_order.2 ⟨fun l hl => _, fun L hL => _⟩
    ·
      refine' eventually_at_top.2 ⟨1, fun n hn => hl.trans_le (h.lim_le_div hbdd (zero_lt_one.trans_le hn).ne')⟩
    ·
      obtain ⟨n, npos, hn⟩ : ∃ n : ℕ, 0 < n ∧ u n / n < L
      ·
        rw [Subadditive.lim] at hL 
        rcases
          exists_lt_of_cInf_lt
            (by 
              simp )
            hL with
          ⟨x, hx, xL⟩
        rcases(mem_image _ _ _).1 hx with ⟨n, hn, rfl⟩
        exact ⟨n, zero_lt_one.trans_le hn, xL⟩
      exact h.eventually_div_lt_of_div_lt npos.ne' hn

end Subadditive

