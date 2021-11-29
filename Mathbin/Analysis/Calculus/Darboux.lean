import Mathbin.Analysis.Calculus.LocalExtr

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/


open Filter Set

open_locale TopologicalSpace Classical

variable{a b : ℝ}{f f' : ℝ → ℝ}

-- error in Analysis.Calculus.Darboux: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Darboux's theorem**: if `a ≤ b` and `f' a < m < f' b`, then `f' c = m` for some
`c ∈ [a, b]`. -/
theorem exists_has_deriv_within_at_eq_of_gt_of_lt
(hab : «expr ≤ »(a, b))
(hf : ∀ x «expr ∈ » Icc a b, has_deriv_within_at f (f' x) (Icc a b) x)
{m : exprℝ()}
(hma : «expr < »(f' a, m))
(hmb : «expr < »(m, f' b)) : «expr ∈ »(m, «expr '' »(f', Icc a b)) :=
begin
  have [ident hab'] [":", expr «expr < »(a, b)] [],
  { refine [expr lt_of_le_of_ne hab (λ hab', _)],
    subst [expr b],
    exact [expr lt_asymm hma hmb] },
  set [] [ident g] [":", expr exprℝ() → exprℝ()] [":="] [expr λ x, «expr - »(f x, «expr * »(m, x))] [],
  have [ident hg] [":", expr ∀ x «expr ∈ » Icc a b, has_deriv_within_at g «expr - »(f' x, m) (Icc a b) x] [],
  { intros [ident x, ident hx],
    simpa [] [] [] [] [] ["using", expr (hf x hx).sub ((has_deriv_within_at_id x _).const_mul m)] },
  obtain ["⟨", ident c, ",", ident cmem, ",", ident hc, "⟩", ":", expr «expr∃ , »((c «expr ∈ » Icc a b), is_min_on g (Icc a b) c)],
  from [expr is_compact_Icc.exists_forall_le «expr $ »(nonempty_Icc.2, hab) (λ x hx, (hg x hx).continuous_within_at)],
  have [ident cmem'] [":", expr «expr ∈ »(c, Ioo a b)] [],
  { cases [expr eq_or_lt_of_le cmem.1] ["with", ident hac, ident hac],
    { subst [expr c],
      refine [expr absurd «expr $ »(sub_nonneg.1, nonneg_of_mul_nonneg_left _ (sub_pos.2 hab')) (not_le_of_lt hma)],
      have [] [":", expr «expr ∈ »(«expr - »(b, a), pos_tangent_cone_at (Icc a b) a)] [],
      from [expr mem_pos_tangent_cone_at_of_segment_subset «expr ▸ »(segment_eq_Icc hab, subset.refl _)],
      simpa [] [] [] ["[", "-", ident sub_nonneg, ",", "-", ident continuous_linear_map.map_sub, "]"] [] ["using", expr hc.localize.has_fderiv_within_at_nonneg (hg a (left_mem_Icc.2 hab)) this] },
    cases [expr eq_or_lt_of_le cmem.2] ["with", ident hbc, ident hbc],
    { subst [expr c],
      refine [expr absurd «expr $ »(sub_nonpos.1, nonpos_of_mul_nonneg_right _ (sub_lt_zero.2 hab')) (not_le_of_lt hmb)],
      have [] [":", expr «expr ∈ »(«expr - »(a, b), pos_tangent_cone_at (Icc a b) b)] [],
      from [expr mem_pos_tangent_cone_at_of_segment_subset (by rw ["[", expr segment_symm, ",", expr segment_eq_Icc hab, "]"] [])],
      simpa [] [] [] ["[", "-", ident sub_nonneg, ",", "-", ident continuous_linear_map.map_sub, "]"] [] ["using", expr hc.localize.has_fderiv_within_at_nonneg (hg b (right_mem_Icc.2 hab)) this] },
    exact [expr ⟨hac, hbc⟩] },
  use ["[", expr c, ",", expr cmem, "]"],
  rw ["[", "<-", expr sub_eq_zero, "]"] [],
  have [] [":", expr «expr ∈ »(Icc a b, expr𝓝() c)] [],
  by rwa ["[", "<-", expr mem_interior_iff_mem_nhds, ",", expr interior_Icc, "]"] [],
  exact [expr (hc.is_local_min this).has_deriv_at_eq_zero ((hg c cmem).has_deriv_at this)]
end

/-- **Darboux's theorem**: if `a ≤ b` and `f' a > m > f' b`, then `f' c = m` for some `c ∈ [a, b]`.
-/
theorem exists_has_deriv_within_at_eq_of_lt_of_gt (hab : a ≤ b)
  (hf : ∀ x (_ : x ∈ Icc a b), HasDerivWithinAt f (f' x) (Icc a b) x) {m : ℝ} (hma : m < f' a) (hmb : f' b < m) :
  m ∈ f' '' Icc a b :=
  let ⟨c, cmem, hc⟩ :=
    exists_has_deriv_within_at_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma) (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩

-- error in Analysis.Calculus.Darboux: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/-- **Darboux's theorem**: the image of a convex set under `f'` is a convex set. -/
theorem convex_image_has_deriv_at
{s : set exprℝ()}
(hs : convex exprℝ() s)
(hf : ∀ x «expr ∈ » s, has_deriv_at f (f' x) x) : convex exprℝ() «expr '' »(f', s) :=
begin
  refine [expr ord_connected.convex ⟨_⟩],
  rintros ["_", "⟨", ident a, ",", ident ha, ",", ident rfl, "⟩", "_", "⟨", ident b, ",", ident hb, ",", ident rfl, "⟩", ident m, "⟨", ident hma, ",", ident hmb, "⟩"],
  cases [expr eq_or_lt_of_le hma] ["with", ident hma, ident hma],
  by exact [expr «expr ▸ »(hma, mem_image_of_mem f' ha)],
  cases [expr eq_or_lt_of_le hmb] ["with", ident hmb, ident hmb],
  by exact [expr «expr ▸ »(hmb.symm, mem_image_of_mem f' hb)],
  cases [expr le_total a b] ["with", ident hab, ident hab],
  { have [] [":", expr «expr ⊆ »(Icc a b, s)] [],
    from [expr hs.ord_connected.out ha hb],
    rcases [expr exists_has_deriv_within_at_eq_of_gt_of_lt hab (λ
      x
      hx, «expr $ »(hf x, this hx).has_deriv_within_at) hma hmb, "with", "⟨", ident c, ",", ident cmem, ",", ident hc, "⟩"],
    exact [expr ⟨c, this cmem, hc⟩] },
  { have [] [":", expr «expr ⊆ »(Icc b a, s)] [],
    from [expr hs.ord_connected.out hb ha],
    rcases [expr exists_has_deriv_within_at_eq_of_lt_of_gt hab (λ
      x
      hx, «expr $ »(hf x, this hx).has_deriv_within_at) hmb hma, "with", "⟨", ident c, ",", ident cmem, ",", ident hc, "⟩"],
    exact [expr ⟨c, this cmem, hc⟩] }
end

/-- If the derivative of a function is never equal to `m`, then either
it is always greater than `m`, or it is always less than `m`. -/
theorem deriv_forall_lt_or_forall_gt_of_forall_ne {s : Set ℝ} (hs : Convex ℝ s)
  (hf : ∀ x (_ : x ∈ s), HasDerivAt f (f' x) x) {m : ℝ} (hf' : ∀ x (_ : x ∈ s), f' x ≠ m) :
  (∀ x (_ : x ∈ s), f' x < m) ∨ ∀ x (_ : x ∈ s), m < f' x :=
  by 
    contrapose! hf' 
    rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
    exact
      (convex_image_has_deriv_at hs hf).OrdConnected.out (mem_image_of_mem f' ha) (mem_image_of_mem f' hb) ⟨hma, hmb⟩

