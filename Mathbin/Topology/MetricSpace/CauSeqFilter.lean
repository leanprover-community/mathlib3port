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

variable {β : Type v}

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
theorem
  CauSeq.tendsto_limit
  [ NormedRing β ] [ hn : IsAbsoluteValue ( norm : β → ℝ ) ] ( f : CauSeq β norm ) [ CauSeq.IsComplete β norm ]
    : tendsto f at_top 𝓝 f.lim
  :=
    _root_.tendsto_nhds . mpr
      by
        intro s os lfs
          suffices : ∃ a : ℕ , ∀ b : ℕ , b ≥ a → f b ∈ s
          · simpa using this
          rcases Metric.is_open_iff . 1 os _ lfs with ⟨ ε , ⟨ hε , hεs ⟩ ⟩
          cases' Setoidₓ.symm CauSeq.equiv_lim f _ hε with N hN
          exists N
          intro b hb
          apply hεs
          dsimp [ Metric.Ball ]
          rw [ dist_comm , dist_eq_norm ]
          solveByElim

variable [NormedField β]

instance NormedField.is_absolute_value : IsAbsoluteValue (norm : β → ℝ) :=
  { abv_nonneg := norm_nonneg, abv_eq_zero := fun _ => norm_eq_zero, abv_add := norm_add_le,
    abv_mul := NormedField.norm_mul }

open Metric

-- failed to parenthesize: no declaration of attribute [parenthesizer] found for 'Lean.Meta.solveByElim'
-- failed to format: no declaration of attribute [formatter] found for 'Lean.Meta.solveByElim'
theorem
  CauchySeq.is_cau_seq
  { f : ℕ → β } ( hf : CauchySeq f ) : IsCauSeq norm f
  :=
    by
      cases' cauchy_iff . 1 hf with hf1 hf2
        intro ε hε
        rcases hf2 { x | dist x . 1 x . 2 < ε } dist_mem_uniformity hε with ⟨ t , ⟨ ht , htsub ⟩ ⟩
        simp at ht
        cases' ht with N hN
        exists N
        intro j hj
        rw [ ← dist_eq_norm ]
        apply @ htsub ( f j , f N )
        apply Set.mk_mem_prod <;> solveByElim [ le_reflₓ ]

-- failed to parenthesize: parenthesize: uncaught backtrack exception
-- failed to format: format: uncaught backtrack exception
theorem
  CauSeq.cauchy_seq
  ( f : CauSeq β norm ) : CauchySeq f
  :=
    by
      refine' cauchy_iff . 2 ⟨ by infer_instance , fun s hs => _ ⟩
        rcases mem_uniformity_dist . 1 hs with ⟨ ε , ⟨ hε , hεs ⟩ ⟩
        cases' CauSeq.cauchy₂ f hε with N hN
        exists { n | n ≥ N } . Image f
        simp only [ exists_prop , mem_at_top_sets , mem_map , mem_image , ge_iff_le , mem_set_of_eq ]
        constructor
        · exists N intro b hb exists b simp [ hb ]
        ·
          rintro ⟨ a , b ⟩ ⟨ ⟨ a' , ⟨ ha'1 , ha'2 ⟩ ⟩ , ⟨ b' , ⟨ hb'1 , hb'2 ⟩ ⟩ ⟩
            dsimp at ha'1 ha'2 hb'1 hb'2
            rw [ ← ha'2 , ← hb'2 ]
            apply hεs
            rw [ dist_eq_norm ]
            apply hN <;> assumption

/-- In a normed field, `cau_seq` coincides with the usual notion of Cauchy sequences. -/
theorem cau_seq_iff_cauchy_seq {α : Type u} [NormedField α] {u : ℕ → α} : IsCauSeq norm u ↔ CauchySeq u :=
  ⟨fun h => CauSeq.cauchy_seq ⟨u, h⟩, fun h => h.is_cau_seq⟩

/-- A complete normed field is complete as a metric space, as Cauchy sequences converge by
assumption and this suffices to characterize completeness. -/
instance (priority := 100) complete_space_of_cau_seq_complete [CauSeq.IsComplete β norm] : CompleteSpace β :=
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

