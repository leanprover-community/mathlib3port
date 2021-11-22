import Mathbin.Analysis.BoxIntegral.Box.Basic 
import Mathbin.Analysis.SpecificLimits

/-!
# Induction on subboxes

In this file we prove the following induction principle for `box_integral.box`, see
`box_integral.box.subbox_induction_on`. Let `p` be a predicate on `box_integral.box ι`, let `I` be a
box. Suppose that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it is true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true.

## Tags

rectangular box, induction
-/


open Set Finset Function Filter Metric

open_locale Classical TopologicalSpace Filter Ennreal

noncomputable theory

namespace BoxIntegral

namespace Box

variable{ι : Type _}{I J : box ι}

/-- For a box `I`, the hyperplanes passing through its center split `I` into `2 ^ card ι` boxes.
`box_integral.box.split_center_box I s` is one of these boxes. See also
`box_integral.partition.split_center` for the corresponding `box_integral.partition`. -/
def split_center_box (I : box ι) (s : Set ι) : box ι :=
  { lower := s.piecewise (fun i => (I.lower i+I.upper i) / 2) I.lower,
    upper := s.piecewise I.upper fun i => (I.lower i+I.upper i) / 2,
    lower_lt_upper :=
      fun i =>
        by 
          dunfold Set.piecewise 
          splitIfs <;> simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper] }

-- error in Analysis.BoxIntegral.Box.SubboxInduction: ././Mathport/Syntax/Translate/Basic.lean:340:40: in exacts: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
theorem mem_split_center_box
{s : set ι}
{y : ι → exprℝ()} : «expr ↔ »(«expr ∈ »(y, I.split_center_box s), «expr ∧ »(«expr ∈ »(y, I), ∀
  i, «expr ↔ »(«expr < »(«expr / »(«expr + »(I.lower i, I.upper i), 2), y i), «expr ∈ »(i, s)))) :=
begin
  simp [] [] ["only"] ["[", expr split_center_box, ",", expr mem_def, ",", "<-", expr forall_and_distrib, "]"] [] [],
  refine [expr forall_congr (λ i, _)],
  dunfold [ident set.piecewise] [],
  split_ifs [] ["with", ident hs]; simp [] [] ["only"] ["[", expr hs, ",", expr iff_true, ",", expr iff_false, ",", expr not_lt, "]"] [] [],
  exacts ["[", expr ⟨λ
    H, ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩, λ
    H, ⟨H.2, H.1.2⟩⟩, ",", expr ⟨λ
    H, ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩, λ H, ⟨H.1.1, H.2⟩⟩, "]"]
end

theorem split_center_box_le (I : box ι) (s : Set ι) : I.split_center_box s ≤ I :=
  fun x hx => (mem_split_center_box.1 hx).1

theorem disjoint_split_center_box (I : box ι) {s t : Set ι} (h : s ≠ t) :
  Disjoint (I.split_center_box s : Set (ι → ℝ)) (I.split_center_box t) :=
  by 
    rintro y ⟨hs, ht⟩
    apply h 
    ext i 
    rw [mem_coe, mem_split_center_box] at hs ht 
    rw [←hs.2, ←ht.2]

theorem injective_split_center_box (I : box ι) : injective I.split_center_box :=
  fun s t H => by_contra$ fun Hne => (I.disjoint_split_center_box Hne).Ne (nonempty_coe _).ne_empty (H ▸ rfl)

@[simp]
theorem exists_mem_split_center_box {I : box ι} {x : ι → ℝ} : (∃ s, x ∈ I.split_center_box s) ↔ x ∈ I :=
  ⟨fun ⟨s, hs⟩ => I.split_center_box_le s hs,
    fun hx => ⟨{ i | (I.lower i+I.upper i) / 2 < x i }, mem_split_center_box.2 ⟨hx, fun i => Iff.rfl⟩⟩⟩

/-- `box_integral.box.split_center_box` bundled as a `function.embedding`. -/
@[simps]
def split_center_box_emb (I : box ι) : Set ι ↪ box ι :=
  ⟨split_center_box I, injective_split_center_box I⟩

@[simp]
theorem Union_coe_split_center_box (I : box ι) : (⋃s, (I.split_center_box s : Set (ι → ℝ))) = I :=
  by 
    ext x 
    simp 

@[simp]
theorem upper_sub_lower_split_center_box (I : box ι) (s : Set ι) (i : ι) :
  (I.split_center_box s).upper i - (I.split_center_box s).lower i = (I.upper i - I.lower i) / 2 :=
  by 
    byCases' hs : i ∈ s <;> fieldSimp [split_center_box, hs, mul_two, two_mul]

-- error in Analysis.BoxIntegral.Box.SubboxInduction: ././Mathport/Syntax/Translate/Basic.lean:340:40: in by_contra: ././Mathport/Syntax/Translate/Tactic/Basic.lean:41:45: missing argument
/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* `H_ind` : Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split
  it into `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.

* `H_nhds` : For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within
  `I.Icc` such that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I`
  with a coefficient of the form `1 / 2 ^ m`, then `p` is true on `J`.

Then `p I` is true. See also `box_integral.box.subbox_induction_on` for a version using
`box_integral.prepartition.split_center` instead of `box_integral.box.split_center_box`.

The proof still works if we assume `H_ind` only for subboxes `J ≤ I` that are homothetic to `I` with
a coefficient of the form `2⁻ᵐ` but we do not need this generalization yet. -/
@[elab_as_eliminator]
theorem subbox_induction_on'
{p : box ι → exprProp()}
(I : box ι)
(H_ind : ∀ J «expr ≤ » I, ∀ s, p (split_center_box J s) → p J)
(H_nhds : ∀
 z «expr ∈ » I.Icc, «expr∃ , »((U «expr ∈ » «expr𝓝[ ] »(I.Icc, z)), ∀
  (J «expr ≤ » I)
  (m : exprℕ()), «expr ∈ »(z, J.Icc) → «expr ⊆ »(J.Icc, U) → ∀
  i, «expr = »(«expr - »(J.upper i, J.lower i), «expr / »(«expr - »(I.upper i, I.lower i), «expr ^ »(2, m))) → p J)) : p I :=
begin
  by_contra [ident hpI],
  replace [ident H_ind] [] [":=", expr λ J hJ, not_imp_not.2 (H_ind J hJ)],
  simp [] [] ["only"] ["[", expr exists_imp_distrib, ",", expr not_forall, "]"] [] ["at", ident H_ind],
  choose ["!"] [ident s] [ident hs] ["using", expr H_ind],
  set [] [ident J] [":", expr exprℕ() → box ι] [":="] [expr λ m, «expr ^[ ]»(λ J, split_center_box J (s J), m) I] [],
  have [ident J_succ] [":", expr ∀
   m, «expr = »(J «expr + »(m, 1), split_center_box (J m) «expr $ »(s, J m))] [":=", expr λ
   m, iterate_succ_apply' _ _ _],
  have [ident hJmono] [":", expr antitone J] [],
  from [expr antitone_nat_of_succ_le (λ
    n, by simpa [] [] [] ["[", expr J_succ, "]"] [] ["using", expr split_center_box_le _ _])],
  have [ident hJle] [":", expr ∀ m, «expr ≤ »(J m, I)] [],
  from [expr λ m, hJmono (zero_le m)],
  have [ident hJp] [":", expr ∀ m, «expr¬ »(p (J m))] [],
  from [expr λ
   m, nat.rec_on m hpI (λ m, by simpa [] [] ["only"] ["[", expr J_succ, "]"] [] ["using", expr hs (J m) (hJle m)])],
  have [ident hJsub] [":", expr ∀
   m
   i, «expr = »(«expr - »((J m).upper i, (J m).lower i), «expr / »(«expr - »(I.upper i, I.lower i), «expr ^ »(2, m)))] [],
  { intros [ident m, ident i],
    induction [expr m] [] ["with", ident m, ident ihm] [],
    { simp [] [] [] ["[", expr J, "]"] [] [] },
    simp [] [] ["only"] ["[", expr pow_succ', ",", expr J_succ, ",", expr upper_sub_lower_split_center_box, ",", expr ihm, ",", expr div_div_eq_div_mul, "]"] [] [] },
  have [ident h0] [":", expr «expr = »(J 0, I)] [],
  from [expr rfl],
  clear_value [ident J],
  clear [ident hpI, ident hs, ident J_succ, ident s],
  set [] [ident z] [":", expr ι → exprℝ()] [":="] [expr «expr⨆ , »((m), (J m).lower)] [],
  have [ident hzJ] [":", expr ∀ m, «expr ∈ »(z, (J m).Icc)] [],
  from [expr mem_Inter.1 (csupr_mem_Inter_Icc_of_antitone_Icc ((@box.Icc ι).monotone.comp_antitone hJmono) (λ
     m, (J m).lower_le_upper))],
  have [ident hJl_mem] [":", expr ∀ m, «expr ∈ »((J m).lower, I.Icc)] [],
  from [expr λ m, le_iff_Icc.1 (hJle m) (J m).lower_mem_Icc],
  have [ident hJu_mem] [":", expr ∀ m, «expr ∈ »((J m).upper, I.Icc)] [],
  from [expr λ m, le_iff_Icc.1 (hJle m) (J m).upper_mem_Icc],
  have [ident hJlz] [":", expr tendsto (λ m, (J m).lower) at_top (expr𝓝() z)] [],
  from [expr tendsto_at_top_csupr (antitone_lower.comp hJmono) ⟨I.upper, λ (x) ⟨m, hm⟩, «expr ▸ »(hm, (hJl_mem m).2)⟩],
  have [ident hJuz] [":", expr tendsto (λ m, (J m).upper) at_top (expr𝓝() z)] [],
  { suffices [] [":", expr tendsto (λ m, «expr - »((J m).upper, (J m).lower)) at_top (expr𝓝() 0)],
    by simpa [] [] [] [] [] ["using", expr hJlz.add this],
    refine [expr tendsto_pi.2 (λ i, _)],
    simpa [] [] [] ["[", expr hJsub, "]"] [] ["using", expr tendsto_const_nhds.div_at_top (tendsto_pow_at_top_at_top_of_one_lt (@one_lt_two exprℝ() _ _))] },
  replace [ident hJlz] [":", expr tendsto (λ m, (J m).lower) at_top «expr𝓝[ ] »(Icc I.lower I.upper, z)] [],
  from [expr tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJlz (eventually_of_forall hJl_mem)],
  replace [ident hJuz] [":", expr tendsto (λ m, (J m).upper) at_top «expr𝓝[ ] »(Icc I.lower I.upper, z)] [],
  from [expr tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJuz (eventually_of_forall hJu_mem)],
  rcases [expr H_nhds z «expr ▸ »(h0, hzJ 0), "with", "⟨", ident U, ",", ident hUz, ",", ident hU, "⟩"],
  rcases [expr (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists, "with", "⟨", ident m, ",", ident hUm, "⟩"],
  exact [expr hJp m (hU (J m) (hJle m) m (hzJ m) hUm (hJsub m))]
end

end Box

end BoxIntegral

