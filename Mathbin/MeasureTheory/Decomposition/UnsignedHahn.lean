import Mathbin.MeasureTheory.Measure.MeasureSpace

/-!
# Unsigned Hahn decomposition theorem

This file proves the unsigned version of the Hahn decomposition theorem.

## Main statements

* `hahn_decomposition` : Given two finite measures `μ` and `ν`, there exists a measurable set `s`
    such that any measurable set `t` included in `s` satisfies `ν t ≤ μ t`, and any
    measurable set `u` included in the complement of `s` satisfies `μ u ≤ ν u`.

## Tags

Hahn decomposition
-/


open Set Filter

open_locale Classical TopologicalSpace Ennreal

namespace MeasureTheory

variable{α : Type _}[MeasurableSpace α]{μ ν : Measureₓ α}

private theorem aux {m : ℕ} {γ d : ℝ} (h : γ - (1 / 2) ^ m < d) : ((γ - 2*(1 / 2) ^ m)+(1 / 2) ^ m) ≤ d :=
  by 
    linarith

-- error in MeasureTheory.Decomposition.UnsignedHahn: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Hahn decomposition theorem** -/
theorem hahn_decomposition
[is_finite_measure μ]
[is_finite_measure ν] : «expr∃ , »((s), «expr ∧ »(measurable_set s, «expr ∧ »(∀
   t, measurable_set t → «expr ⊆ »(t, s) → «expr ≤ »(ν t, μ t), ∀
   t, measurable_set t → «expr ⊆ »(t, «expr ᶜ»(s)) → «expr ≤ »(μ t, ν t)))) :=
begin
  let [ident d] [":", expr set α → exprℝ()] [":=", expr λ s, «expr - »(((μ s).to_nnreal : exprℝ()), (ν s).to_nnreal)],
  let [ident c] [":", expr set exprℝ()] [":=", expr «expr '' »(d, {s | measurable_set s})],
  let [ident γ] [":", expr exprℝ()] [":=", expr Sup c],
  have [ident hμ] [":", expr ∀ s, «expr ≠ »(μ s, «expr∞»())] [":=", expr measure_ne_top μ],
  have [ident hν] [":", expr ∀ s, «expr ≠ »(ν s, «expr∞»())] [":=", expr measure_ne_top ν],
  have [ident to_nnreal_μ] [":", expr ∀
   s, «expr = »(((μ s).to_nnreal : «exprℝ≥0∞»()), μ s)] [":=", expr assume s, «expr $ »(ennreal.coe_to_nnreal, hμ _)],
  have [ident to_nnreal_ν] [":", expr ∀
   s, «expr = »(((ν s).to_nnreal : «exprℝ≥0∞»()), ν s)] [":=", expr assume s, «expr $ »(ennreal.coe_to_nnreal, hν _)],
  have [ident d_empty] [":", expr «expr = »(d «expr∅»(), 0)] [],
  { change [expr «expr = »(«expr - »(_, _), _)] [] [],
    rw ["[", expr measure_empty, ",", expr measure_empty, ",", expr sub_self, "]"] [] },
  have [ident d_split] [":", expr ∀
   s t, measurable_set s → measurable_set t → «expr = »(d s, «expr + »(d «expr \ »(s, t), d «expr ∩ »(s, t)))] [],
  { assume [binders (s t hs ht)],
    simp [] [] ["only"] ["[", expr d, "]"] [] [],
    rw ["[", "<-", expr measure_inter_add_diff s ht, ",", "<-", expr measure_inter_add_diff s ht, ",", expr ennreal.to_nnreal_add (hμ _) (hμ _), ",", expr ennreal.to_nnreal_add (hν _) (hν _), ",", expr nnreal.coe_add, ",", expr nnreal.coe_add, "]"] [],
    simp [] [] ["only"] ["[", expr sub_eq_add_neg, ",", expr neg_add, "]"] [] [],
    ac_refl },
  have [ident d_Union] [":", expr ∀
   s : exprℕ() → set α, ∀
   n, measurable_set (s n) → monotone s → tendsto (λ n, d (s n)) at_top (expr𝓝() (d «expr⋃ , »((n), s n)))] [],
  { assume [binders (s hs hm)],
    refine [expr tendsto.sub _ _]; refine [expr «expr $ »(nnreal.tendsto_coe.2, «expr $ »((ennreal.tendsto_to_nnreal _).comp, tendsto_measure_Union hs hm))],
    exact [expr hμ _],
    exact [expr hν _] },
  have [ident d_Inter] [":", expr ∀
   s : exprℕ() → set α, ∀
   n, measurable_set (s n) → ∀
   n m, «expr ≤ »(n, m) → «expr ⊆ »(s m, s n) → tendsto (λ n, d (s n)) at_top (expr𝓝() (d «expr⋂ , »((n), s n)))] [],
  { assume [binders (s hs hm)],
    refine [expr tendsto.sub _ _]; refine [expr «expr $ »(nnreal.tendsto_coe.2, «expr $ »(«expr $ »(ennreal.tendsto_to_nnreal, _).comp, tendsto_measure_Inter hs hm _))],
    exacts ["[", expr hμ _, ",", expr ⟨0, hμ _⟩, ",", expr hν _, ",", expr ⟨0, hν _⟩, "]"] },
  have [ident bdd_c] [":", expr bdd_above c] [],
  { use [expr (μ univ).to_nnreal],
    rintros [ident r, "⟨", ident s, ",", ident hs, ",", ident rfl, "⟩"],
    refine [expr le_trans «expr $ »(sub_le_self _, nnreal.coe_nonneg _) _],
    rw ["[", expr nnreal.coe_le_coe, ",", "<-", expr ennreal.coe_le_coe, ",", expr to_nnreal_μ, ",", expr to_nnreal_μ, "]"] [],
    exact [expr measure_mono (subset_univ _)] },
  have [ident c_nonempty] [":", expr c.nonempty] [":=", expr nonempty.image _ ⟨_, measurable_set.empty⟩],
  have [ident d_le_γ] [":", expr ∀
   s, measurable_set s → «expr ≤ »(d s, γ)] [":=", expr assume s hs, le_cSup bdd_c ⟨s, hs, rfl⟩],
  have [] [":", expr ∀
   n : exprℕ(), «expr∃ , »((s : set α), «expr ∧ »(measurable_set s, «expr < »(«expr - »(γ, «expr ^ »(«expr / »(1, 2), n)), d s)))] [],
  { assume [binders (n)],
    have [] [":", expr «expr < »(«expr - »(γ, «expr ^ »(«expr / »(1, 2), n)), γ)] [":=", expr sub_lt_self γ (pow_pos (half_pos zero_lt_one) n)],
    rcases [expr exists_lt_of_lt_cSup c_nonempty this, "with", "⟨", ident r, ",", "⟨", ident s, ",", ident hs, ",", ident rfl, "⟩", ",", ident hlt, "⟩"],
    exact [expr ⟨s, hs, hlt⟩] },
  rcases [expr classical.axiom_of_choice this, "with", "⟨", ident e, ",", ident he, "⟩"],
  change [expr exprℕ() → set α] [] ["at", ident e],
  have [ident he₁] [":", expr ∀ n, measurable_set (e n)] [":=", expr assume n, (he n).1],
  have [ident he₂] [":", expr ∀
   n, «expr < »(«expr - »(γ, «expr ^ »(«expr / »(1, 2), n)), d (e n))] [":=", expr assume n, (he n).2],
  let [ident f] [":", expr exprℕ() → exprℕ() → set α] [":=", expr λ n m, (finset.Ico n «expr + »(m, 1)).inf e],
  have [ident hf] [":", expr ∀ n m, measurable_set (f n m)] [],
  { assume [binders (n m)],
    simp [] [] ["only"] ["[", expr f, ",", expr finset.inf_eq_infi, "]"] [] [],
    exact [expr measurable_set.bInter (countable_encodable _) (assume i _, he₁ _)] },
  have [ident f_subset_f] [":", expr ∀ {a b c d}, «expr ≤ »(a, b) → «expr ≤ »(c, d) → «expr ⊆ »(f a d, f b c)] [],
  { assume [binders (a b c d hab hcd)],
    dsimp ["only"] ["[", expr f, "]"] [] [],
    rw ["[", expr finset.inf_eq_infi, ",", expr finset.inf_eq_infi, "]"] [],
    exact [expr bInter_subset_bInter_left «expr $ »(finset.Ico_subset_Ico hab, nat.succ_le_succ hcd)] },
  have [ident f_succ] [":", expr ∀
   n m, «expr ≤ »(n, m) → «expr = »(f n «expr + »(m, 1), «expr ∩ »(f n m, e «expr + »(m, 1)))] [],
  { assume [binders (n m hnm)],
    have [] [":", expr «expr ≤ »(n, «expr + »(m, 1))] [":=", expr le_of_lt (nat.succ_le_succ hnm)],
    simp [] [] ["only"] ["[", expr f, "]"] [] [],
    rw ["[", expr nat.Ico_succ_right_eq_insert_Ico this, ",", expr finset.inf_insert, ",", expr set.inter_comm, "]"] [],
    refl },
  have [ident le_d_f] [":", expr ∀
   n
   m, «expr ≤ »(m, n) → «expr ≤ »(«expr + »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), «expr ^ »(«expr / »(1, 2), n)), d (f m n))] [],
  { assume [binders (n m h)],
    refine [expr nat.le_induction _ _ n h],
    { have [] [] [":=", expr he₂ m],
      simp [] [] ["only"] ["[", expr f, "]"] [] [],
      rw ["[", expr nat.Ico_succ_singleton, ",", expr finset.inf_singleton, "]"] [],
      exact [expr aux this] },
    { assume [binders (n) (hmn : «expr ≤ »(m, n)) (ih)],
      have [] [":", expr «expr ≤ »(«expr + »(γ, «expr + »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), «expr ^ »(«expr / »(1, 2), «expr + »(n, 1)))), «expr + »(γ, d (f m «expr + »(n, 1))))] [],
      { calc
          «expr ≤ »(«expr + »(γ, «expr + »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), «expr ^ »(«expr / »(1, 2), «expr + »(n, 1)))), «expr + »(γ, «expr + »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), «expr - »(«expr ^ »(«expr / »(1, 2), n), «expr ^ »(«expr / »(1, 2), «expr + »(n, 1)))))) : begin
            refine [expr add_le_add_left (add_le_add_left _ _) γ],
            simp [] [] ["only"] ["[", expr pow_add, ",", expr pow_one, ",", expr le_sub_iff_add_le, "]"] [] [],
            linarith [] [] []
          end
          «expr = »(..., «expr + »(«expr - »(γ, «expr ^ »(«expr / »(1, 2), «expr + »(n, 1))), «expr + »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), «expr ^ »(«expr / »(1, 2), n)))) : by simp [] [] ["only"] ["[", expr sub_eq_add_neg, "]"] [] []; ac_refl
          «expr ≤ »(..., «expr + »(d (e «expr + »(n, 1)), d (f m n))) : add_le_add «expr $ »(le_of_lt, he₂ _) ih
          «expr ≤ »(..., «expr + »(«expr + »(d (e «expr + »(n, 1)), d «expr \ »(f m n, e «expr + »(n, 1))), d (f m «expr + »(n, 1)))) : by rw ["[", expr f_succ _ _ hmn, ",", expr d_split (f m n) (e «expr + »(n, 1)) (hf _ _) (he₁ _), ",", expr add_assoc, "]"] []
          «expr = »(..., «expr + »(d «expr ∪ »(e «expr + »(n, 1), f m n), d (f m «expr + »(n, 1)))) : begin
            rw ["[", expr d_split «expr ∪ »(e «expr + »(n, 1), f m n) (e «expr + »(n, 1)), ",", expr union_diff_left, ",", expr union_inter_cancel_left, "]"] [],
            ac_refl,
            exact [expr (he₁ _).union (hf _ _)],
            exact [expr he₁ _]
          end
          «expr ≤ »(..., «expr + »(γ, d (f m «expr + »(n, 1)))) : add_le_add_right «expr $ »(d_le_γ _, (he₁ _).union (hf _ _)) _ },
      exact [expr (add_le_add_iff_left γ).1 this] } },
  let [ident s] [] [":=", expr «expr⋃ , »((m), «expr⋂ , »((n), f m n))],
  have [ident γ_le_d_s] [":", expr «expr ≤ »(γ, d s)] [],
  { have [ident hγ] [":", expr tendsto (λ
      m : exprℕ(), «expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m)))) at_top (expr𝓝() γ)] [],
    { suffices [] [":", expr tendsto (λ
        m : exprℕ(), «expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m)))) at_top (expr𝓝() «expr - »(γ, «expr * »(2, 0)))],
      { simpa [] [] [] [] [] [] },
      exact [expr «expr $ »(tendsto_const_nhds.sub, «expr $ »(tendsto_const_nhds.mul, tendsto_pow_at_top_nhds_0_of_lt_1 «expr $ »(le_of_lt, «expr $ »(half_pos, zero_lt_one)) (half_lt_self zero_lt_one)))] },
    have [ident hd] [":", expr tendsto (λ
      m, d «expr⋂ , »((n), f m n)) at_top (expr𝓝() (d «expr⋃ , »((m), «expr⋂ , »((n), f m n))))] [],
    { refine [expr d_Union _ _ _],
      { assume [binders (n)],
        exact [expr measurable_set.Inter (assume m, hf _ _)] },
      { exact [expr assume
         n
         m
         hnm, subset_Inter (assume
          i, «expr $ »(subset.trans (Inter_subset (f n) i), «expr $ »(f_subset_f hnm, le_refl _)))] } },
    refine [expr le_of_tendsto_of_tendsto' hγ hd (assume m, _)],
    have [] [":", expr tendsto (λ n, d (f m n)) at_top (expr𝓝() (d «expr⋂ , »((n), f m n)))] [],
    { refine [expr d_Inter _ _ _],
      { assume [binders (n)],
        exact [expr hf _ _] },
      { assume [binders (n m hnm)],
        exact [expr f_subset_f (le_refl _) hnm] } },
    refine [expr ge_of_tendsto this (eventually_at_top.2 ⟨m, assume n hmn, _⟩)],
    change [expr «expr ≤ »(«expr - »(γ, «expr * »(2, «expr ^ »(«expr / »(1, 2), m))), d (f m n))] [] [],
    refine [expr le_trans _ (le_d_f _ _ hmn)],
    exact [expr le_add_of_le_of_nonneg (le_refl _) (pow_nonneg «expr $ »(le_of_lt, «expr $ »(half_pos, zero_lt_one)) _)] },
  have [ident hs] [":", expr measurable_set s] [":=", expr measurable_set.Union (assume
    n, measurable_set.Inter (assume m, hf _ _))],
  refine [expr ⟨s, hs, _, _⟩],
  { assume [binders (t ht hts)],
    have [] [":", expr «expr ≤ »(0, d t)] [":=", expr «expr $ »((add_le_add_iff_left γ).1, calc
        «expr ≤ »(«expr + »(γ, 0), d s) : by rw ["[", expr add_zero, "]"] []; exact [expr γ_le_d_s]
        «expr = »(..., «expr + »(d «expr \ »(s, t), d t)) : by rw ["[", expr d_split _ _ hs ht, ",", expr inter_eq_self_of_subset_right hts, "]"] []
        «expr ≤ »(..., «expr + »(γ, d t)) : add_le_add (d_le_γ _ (hs.diff ht)) (le_refl _))],
    rw ["[", "<-", expr to_nnreal_μ, ",", "<-", expr to_nnreal_ν, ",", expr ennreal.coe_le_coe, ",", "<-", expr nnreal.coe_le_coe, "]"] [],
    simpa [] [] ["only"] ["[", expr d, ",", expr le_sub_iff_add_le, ",", expr zero_add, "]"] [] ["using", expr this] },
  { assume [binders (t ht hts)],
    have [] [":", expr «expr ≤ »(d t, 0)] [],
    exact [expr «expr $ »((add_le_add_iff_left γ).1, calc
        «expr ≤ »(«expr + »(γ, d t), «expr + »(d s, d t)) : add_le_add γ_le_d_s (le_refl _)
        «expr = »(..., d «expr ∪ »(s, t)) : begin
          rw ["[", expr d_split _ _ (hs.union ht) ht, ",", expr union_diff_right, ",", expr union_inter_cancel_right, ",", expr diff_eq_self.2, "]"] [],
          exact [expr assume (a) ⟨hat, has⟩, hts hat has]
        end
        «expr ≤ »(..., «expr + »(γ, 0)) : by rw ["[", expr add_zero, "]"] []; exact [expr d_le_γ _ (hs.union ht)])],
    rw ["[", "<-", expr to_nnreal_μ, ",", "<-", expr to_nnreal_ν, ",", expr ennreal.coe_le_coe, ",", "<-", expr nnreal.coe_le_coe, "]"] [],
    simpa [] [] ["only"] ["[", expr d, ",", expr sub_le_iff_le_add, ",", expr zero_add, "]"] [] ["using", expr this] }
end

end MeasureTheory

