import Mathbin.Analysis.NormedSpace.Basic

/-!
# Completeness in terms of `cauchy` filters vs `is_cau_seq` sequences

In this file we apply `metric.complete_of_cauchy_seq_tendsto` to prove that a `normed_ring`
is complete in terms of `cauchy` filter if and only if it is complete in terms
of `cau_seq` Cauchy sequences.
-/


universe u v

open Set Filter

open_locale TopologicalSpace Classical

variable{β : Type v}

-- error in Topology.MetricSpace.CauSeqFilter: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem cau_seq.tendsto_limit
[normed_ring β]
[hn : is_absolute_value (norm : β → exprℝ())]
(f : cau_seq β norm)
[cau_seq.is_complete β norm] : tendsto f at_top (expr𝓝() f.lim) :=
_root_.tendsto_nhds.mpr (begin
   intros [ident s, ident os, ident lfs],
   suffices [] [":", expr «expr∃ , »((a : exprℕ()), ∀ b : exprℕ(), «expr ≥ »(b, a) → «expr ∈ »(f b, s))],
   by simpa [] [] [] [] [] ["using", expr this],
   rcases [expr metric.is_open_iff.1 os _ lfs, "with", "⟨", ident ε, ",", "⟨", ident hε, ",", ident hεs, "⟩", "⟩"],
   cases [expr setoid.symm (cau_seq.equiv_lim f) _ hε] ["with", ident N, ident hN],
   existsi [expr N],
   intros [ident b, ident hb],
   apply [expr hεs],
   dsimp [] ["[", expr metric.ball, "]"] [] [],
   rw ["[", expr dist_comm, ",", expr dist_eq_norm, "]"] [],
   solve_by_elim [] [] [] []
 end)

variable[NormedField β]

instance NormedField.is_absolute_value : IsAbsoluteValue (norm : β → ℝ) :=
  { abv_nonneg := norm_nonneg, abv_eq_zero := fun _ => norm_eq_zero, abv_add := norm_add_le,
    abv_mul := NormedField.norm_mul }

open Metric

-- error in Topology.MetricSpace.CauSeqFilter: ././Mathport/Syntax/Translate/Basic.lean:176:17: failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
theorem cauchy_seq.is_cau_seq {f : exprℕ() → β} (hf : cauchy_seq f) : is_cau_seq norm f :=
begin
  cases [expr cauchy_iff.1 hf] ["with", ident hf1, ident hf2],
  intros [ident ε, ident hε],
  rcases [expr hf2 {x | «expr < »(dist x.1 x.2, ε)} (dist_mem_uniformity hε), "with", "⟨", ident t, ",", "⟨", ident ht, ",", ident htsub, "⟩", "⟩"],
  simp [] [] [] [] [] ["at", ident ht],
  cases [expr ht] ["with", ident N, ident hN],
  existsi [expr N],
  intros [ident j, ident hj],
  rw ["<-", expr dist_eq_norm] [],
  apply [expr @htsub (f j, f N)],
  apply [expr set.mk_mem_prod]; solve_by_elim [] [] ["[", expr le_refl, "]"] []
end

theorem CauSeq.cauchy_seq (f : CauSeq β norm) : CauchySeq f :=
  by 
    refine'
      cauchy_iff.2
        ⟨by 
            infer_instance,
          fun s hs => _⟩
    rcases mem_uniformity_dist.1 hs with ⟨ε, ⟨hε, hεs⟩⟩
    cases' CauSeq.cauchy₂ f hε with N hN 
    exists { n | n ≥ N }.Image f 
    simp only [exists_prop, mem_at_top_sets, mem_map, mem_image, ge_iff_le, mem_set_of_eq]
    split 
    ·
      exists N 
      intro b hb 
      exists b 
      simp [hb]
    ·
      rintro ⟨a, b⟩ ⟨⟨a', ⟨ha'1, ha'2⟩⟩, ⟨b', ⟨hb'1, hb'2⟩⟩⟩
      dsimp  at ha'1 ha'2 hb'1 hb'2 
      rw [←ha'2, ←hb'2]
      apply hεs 
      rw [dist_eq_norm]
      apply hN <;> assumption

/-- In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences. -/
theorem cau_seq_iff_cauchy_seq {α : Type u} [NormedField α] {u : ℕ → α} : IsCauSeq norm u ↔ CauchySeq u :=
  ⟨fun h => CauSeq.cauchy_seq ⟨u, h⟩, fun h => h.is_cau_seq⟩

/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
instance (priority := 100)complete_space_of_cau_seq_complete [CauSeq.IsComplete β norm] : CompleteSpace β :=
  by 
    apply complete_of_cauchy_seq_tendsto 
    intro u hu 
    have C : IsCauSeq norm u := cau_seq_iff_cauchy_seq.2 hu 
    exists CauSeq.lim ⟨u, C⟩
    rw [Metric.tendsto_at_top]
    intro ε εpos 
    cases' (CauSeq.equiv_lim ⟨u, C⟩) _ εpos with N hN 
    exists N 
    simpa [dist_eq_norm] using hN

