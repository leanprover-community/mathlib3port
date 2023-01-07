/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot

! This file was ported from Lean 3 source module topology.algebra.valued_field
! leanprover-community/mathlib commit 6afc9b06856ad973f6a2619e3e8a0a8d537a58f2
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Topology.Algebra.Valuation
import Mathbin.Topology.Algebra.WithZeroTopology
import Mathbin.Topology.Algebra.UniformField

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, ie inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/


open Filter Set

open TopologicalSpace

section DivisionRing

variable {K : Type _} [DivisionRing K] {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable (v : Valuation K Γ₀)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (ie the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
theorem Valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y ≠ 0)
    (h : v (x - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) < γ :=
  by
  have hyp1 : v (x - y) < γ * (v y * v y) := lt_of_lt_of_le h (min_le_left _ _)
  have hyp1' : v (x - y) * (v y * v y)⁻¹ < γ := mul_inv_lt_of_lt_mul₀ hyp1
  have hyp2 : v (x - y) < v y := lt_of_lt_of_le h (min_le_right _ _)
  have key : v x = v y := Valuation.map_eq_of_sub_lt v hyp2
  have x_ne : x ≠ 0 := by
    intro h
    apply y_ne
    rw [h, v.map_zero] at key
    exact v.zero_iff.1 key.symm
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹ := by
    rw [mul_sub_left_distrib, sub_mul, mul_assoc, show y * y⁻¹ = 1 from mul_inv_cancel y_ne,
      show x⁻¹ * x = 1 from inv_mul_cancel x_ne, mul_one, one_mul]
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) := by rw [decomp]
    _ = v x⁻¹ * (v <| y - x) * v y⁻¹ := by repeat' rw [Valuation.map_mul]
    _ = (v x)⁻¹ * (v <| y - x) * (v y)⁻¹ := by rw [map_inv₀, map_inv₀]
    _ = (v <| y - x) * (v y * v y)⁻¹ := by rw [mul_assoc, mul_comm, key, mul_assoc, mul_inv_rev]
    _ = (v <| y - x) * (v y * v y)⁻¹ := rfl
    _ = (v <| x - y) * (v y * v y)⁻¹ := by rw [Valuation.map_sub_swap]
    _ < γ := hyp1'
    
#align valuation.inversion_estimate Valuation.inversion_estimate

end InversionEstimate

open Valued

/-- The topology coming from a valuation on a division ring makes it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100) Valued.topological_division_ring [Valued K Γ₀] :
    TopologicalDivisionRing K :=
  { (by infer_instance : TopologicalRing K) with
    continuous_at_inv₀ := by
      intro x x_ne s s_in
      cases' valued.mem_nhds.mp s_in with γ hs; clear s_in
      rw [mem_map, Valued.mem_nhds]
      change ∃ γ : Γ₀ˣ, { y : K | (v (y - x) : Γ₀) < γ } ⊆ { x : K | x⁻¹ ∈ s }
      have vx_ne := (Valuation.ne_zero_iff <| v).mpr x_ne
      let γ' := Units.mk0 _ vx_ne
      use min (γ * (γ' * γ')) γ'
      intro y y_in
      apply hs
      simp only [mem_set_of_eq] at y_in
      rw [Units.min_val, Units.val_mul, Units.val_mul] at y_in
      exact Valuation.inversion_estimate _ x_ne y_in }
#align valued.topological_division_ring Valued.topological_division_ring

/-- A valued division ring is separated. -/
instance (priority := 100) ValuedRing.separated [Valued K Γ₀] : SeparatedSpace K :=
  by
  rw [separated_iff_t2]
  apply TopologicalAddGroup.t2SpaceOfZeroSep
  intro x x_ne
  refine' ⟨{ k | v k < v x }, _, fun h => lt_irrefl _ h⟩
  rw [Valued.mem_nhds]
  have vx_ne := (Valuation.ne_zero_iff <| v).mpr x_ne
  let γ' := Units.mk0 _ vx_ne
  exact ⟨γ', fun y hy => by simpa using hy⟩
#align valued_ring.separated ValuedRing.separated

section

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

open Valued

theorem Valued.continuous_valuation [Valued K Γ₀] : Continuous (v : K → Γ₀) :=
  by
  rw [continuous_iff_continuous_at]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, LinearOrderedCommGroupWithZero.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    use Units.mk0 γ hγ, subset.rfl
  · have v_ne : (v x : Γ₀) ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, LinearOrderedCommGroupWithZero.tendsto_of_ne_zero v_ne]
    apply Valued.loc_const v_ne
#align valued.continuous_valuation Valued.continuous_valuation

end

end ValuationTopologicalDivisionRing

end DivisionRing

namespace Valued

open UniformSpace

variable {K : Type _} [Field K] {Γ₀ : Type _} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

include hv

-- mathport name: exprhat
local notation "hat " => Completion

/-- A valued field is completable. -/
instance (priority := 100) completable : CompletableTopField K :=
  { ValuedRing.separated with
    nice := by
      rintro F hF h0
      have : ∃ γ₀ : Γ₀ˣ, ∃ M ∈ F, ∀ x ∈ M, (γ₀ : Γ₀) ≤ v x :=
        by
        rcases filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
        rcases valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
        exists γ₀, M, M_in
        intro x xM
        apply le_of_not_lt _
        intro hyp
        have : x ∈ U ∩ M := ⟨hU hyp, xM⟩
        rwa [H] at this
      rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
      rw [Valued.cauchy_iff] at hF⊢
      refine' ⟨hF.1.map _, _⟩
      replace hF := hF.2
      intro γ
      rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
      clear hF
      use (fun x : K => x⁻¹) '' (M₀ ∩ M₁)
      constructor
      · rw [mem_map]
        apply mem_of_superset (Filter.inter_mem M₀_in M₁_in)
        exact subset_preimage_image _ _
      · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩
        simp only [mem_set_of_eq]
        specialize H₁ x x_in₁ y y_in₁
        replace x_in₀ := H₀ x x_in₀
        replace y_in₀ := H₀ y y_in₀
        clear H₀
        apply Valuation.inversion_estimate
        · have : (v x : Γ₀) ≠ 0 := by
            intro h
            rw [h] at x_in₀
            simpa using x_in₀
          exact (Valuation.ne_zero_iff _).mp this
        · refine' lt_of_lt_of_le H₁ _
          rw [Units.min_val]
          apply min_le_min _ x_in₀
          rw [mul_assoc]
          have : ((γ₀ * γ₀ : Γ₀ˣ) : Γ₀) ≤ v x * v x :=
            calc
              ↑γ₀ * ↑γ₀ ≤ ↑γ₀ * v x := mul_le_mul_left' x_in₀ ↑γ₀
              _ ≤ _ := mul_le_mul_right' x_in₀ (v x)
              
          rw [Units.val_mul]
          exact mul_le_mul_left' this γ }
#align valued.completable Valued.completable

attribute [local instance] LinearOrderedCommGroupWithZero.topologicalSpace

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The extension of the valuation of a valued field to the completion of the field. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `extension [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.arrow (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) "→" `Γ₀))])
      (Command.declValSimple
       ":="
       (Term.app
        (Term.proj `Completion.dense_inducing_coe "." `extend)
        [(Term.typeAscription "(" `v ":" [(Term.arrow `K "→" `Γ₀)] ")")])
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `Completion.dense_inducing_coe "." `extend)
       [(Term.typeAscription "(" `v ":" [(Term.arrow `K "→" `Γ₀)] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `v ":" [(Term.arrow `K "→" `Γ₀)] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow `K "→" `Γ₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `v
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `Completion.dense_inducing_coe "." `extend)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Completion.dense_inducing_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) "→" `Γ₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The extension of the valuation of a valued field to the completion of the field. -/
    noncomputable
  def extension : hat K → Γ₀ := Completion.dense_inducing_coe . extend ( v : K → Γ₀ )
#align valued.extension Valued.extension

/- ./././Mathport/Syntax/Translate/Basic.lean:632:2: warning: expanding binder collection (x y «expr ∈ » V') -/
/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `continuous_extension [])
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Continuous
         [(Term.typeAscription
           "("
           `Valued.extension
           ":"
           [(Term.arrow
             (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
             "→"
             `Γ₀)]
           ")")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app `completion.dense_inducing_coe.continuous_extend [(Term.hole "_")]))
           []
           (Tactic.intro "intro" [`x₀])
           []
           (Std.Tactic.rcases
            "rcases"
            [(Tactic.casesTarget [] (Term.app `eq_or_ne [`x₀ (num "0")]))]
            ["with"
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.paren
                 "("
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.one `rfl)
                    "|"
                    (Std.Tactic.RCases.rcasesPat.one `h)])
                  [])
                 ")")])
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(num "0") "," (Term.hole "_")] "⟩"))
             []
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 [(patternIgnore (token.«← » "←"))]
                 `completion.dense_inducing_coe.to_inducing.nhds_eq_comap)]
               "]")
              [])
             []
             (Tactic.exact
              "exact"
              (Term.app
               `valued.continuous_valuation.tendsto'
               [(num "0") (num "0") (Term.app `map_zero [`v])]))])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`preimage_one []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Set.Data.Set.Image.«term_⁻¹'_»
                    `v
                    " ⁻¹' "
                    («term{_}» "{" [(Term.typeAscription "(" (num "1") ":" [`Γ₀] ")")] "}"))
                   "∈"
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.typeAscription "(" (num "1") ":" [`K] ")")])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_≠_»
                          (Term.typeAscription
                           "("
                           (Term.app `v [(Term.typeAscription "(" (num "1") ":" [`K] ")")])
                           ":"
                           [`Γ₀]
                           ")")
                          "≠"
                          (num "0")))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.map_one)] "]")
                            [])
                           []
                           (Tactic.exact "exact" `zero_ne_one.symm)]))))))
                    []
                    (convert "convert" [] (Term.app `Valued.loc_const [`this]) [])
                    []
                    (Std.Tactic.Ext.«tacticExt___:_»
                     "ext"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `Valuation.map_one)
                       ","
                       (Tactic.rwRule [] `mem_preimage)
                       ","
                       (Tactic.rwRule [] `mem_singleton_iff)
                       ","
                       (Tactic.rwRule [] `mem_set_of_eq)]
                      "]")
                     [])]))))))
             []
             (Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_in)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV)])
                    [])]
                  "⟩")])]
              [":"
               (Std.ExtendedBinder.«term∃__,_»
                "∃"
                (Lean.binderIdent `V)
                («binderTerm∈_»
                 "∈"
                 (Term.app
                  (TopologicalSpace.Topology.Basic.nhds "𝓝")
                  [(Term.typeAscription
                    "("
                    (num "1")
                    ":"
                    [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                    ")")]))
                ","
                (Term.forall
                 "∀"
                 [`x]
                 [(Term.typeSpec ":" `K)]
                 ","
                 (Term.arrow
                  («term_∈_»
                   (Term.typeAscription
                    "("
                    `x
                    ":"
                    [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                    ")")
                   "∈"
                   `V)
                  "→"
                  («term_=_»
                   (Term.typeAscription "(" (Term.app `v [`x]) ":" [`Γ₀] ")")
                   "="
                   (num "1")))))]
              [":="
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `completion.dense_inducing_coe.nhds_eq_comap)
                       ","
                       (Tactic.rwRule [] `mem_comap)]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`preimage_one] []))])])))]])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Std.ExtendedBinder.«term∃__,_»
                   "∃"
                   (Lean.binderIdent `V')
                   («binderTerm∈_»
                    "∈"
                    (Term.app
                     (TopologicalSpace.Topology.Basic.nhds "𝓝")
                     [(Term.typeAscription
                       "("
                       (num "1")
                       ":"
                       [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                       ")")]))
                   ","
                   («term_∧_»
                    («term_∉_»
                     (Term.typeAscription
                      "("
                      (num "0")
                      ":"
                      [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                      ")")
                     "∉"
                     `V')
                    "∧"
                    (Term.forall
                     "∀"
                     [(Term.explicitBinder "(" [`x] [] [] ")")
                      (Term.explicitBinder
                       "("
                       [(Term.hole "_")]
                       [":" («term_∈_» `x "∈" `V')]
                       []
                       ")")
                      (Term.explicitBinder "(" [`y] [] [] ")")
                      (Term.explicitBinder
                       "("
                       [(Term.hole "_")]
                       [":" («term_∈_» `y "∈" `V')]
                       []
                       ")")]
                     []
                     ","
                     («term_∈_» («term_*_» `x "*" («term_⁻¹» `y "⁻¹")) "∈" `V)))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `tendsto
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`p]
                             [(Term.typeSpec
                               ":"
                               («term_×_»
                                (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                                "×"
                                (Term.app
                                 (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                 [`K])))]
                             "=>"
                             («term_*_»
                              (Term.proj `p "." (fieldIdx "1"))
                              "*"
                              («term_⁻¹» (Term.proj `p "." (fieldIdx "2")) "⁻¹"))))
                           (Term.app
                            (Term.proj
                             (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])
                             "."
                             `Prod)
                            [(Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])])
                           (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                             "]")
                            [])
                           []
                           (Tactic.Conv.conv
                            "conv"
                            []
                            []
                            "=>"
                            (Tactic.Conv.convSeq
                             (Tactic.Conv.convSeq1Indented
                              [(Tactic.Conv.congr "congr")
                               []
                               (Tactic.Conv.skip "skip")
                               []
                               (Tactic.Conv.skip "skip")
                               []
                               (Tactic.Conv.convRw__
                                "rw"
                                []
                                (Tactic.rwRuleSeq
                                 "["
                                 [(Tactic.rwRule
                                   [(patternIgnore (token.«← » "←"))]
                                   (Term.app
                                    `one_mul
                                    [(Term.typeAscription
                                      "("
                                      (num "1")
                                      ":"
                                      [(Term.app
                                        (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                        [`K])]
                                      ")")]))]
                                 "]"))])))
                           []
                           (Tactic.refine'
                            "refine'"
                            (Term.app
                             `tendsto.mul
                             [`continuous_fst.continuous_at
                              (Term.app
                               `tendsto.comp
                               [(Term.hole "_") `continuous_snd.continuous_at])]))
                           []
                           (convert
                            "convert"
                            []
                            (Term.app
                             `continuous_at_inv₀
                             [(Term.typeAscription
                               "("
                               `zero_ne_one.symm
                               ":"
                               [(«term_≠_»
                                 (num "1")
                                 "≠"
                                 (Term.typeAscription
                                  "("
                                  (num "0")
                                  ":"
                                  [(Term.app
                                    (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                    [`K])]
                                  ")"))]
                               ")")])
                            [])
                           []
                           (Tactic.exact "exact" `inv_one.symm)]))))))
                    []
                    (Std.Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget [] (Term.app `tendsto_prod_self_iff.mp [`this `V `V_in]))]
                     ["with"
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `U_in)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                            [])]
                          "⟩")])
                       [])])
                    []
                    (Tactic.tacticLet_
                     "let"
                     (Term.letDecl
                      (Term.letIdDecl
                       `hatKstar
                       []
                       []
                       ":="
                       (Term.typeAscription
                        "("
                        (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
                        ":"
                        [(«term_<|_»
                          `Set
                          "<|"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        ")"))))
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_∈_»
                          `hatKstar
                          "∈"
                          (Term.app
                           (TopologicalSpace.Topology.Basic.nhds "𝓝")
                           [(Term.typeAscription
                             "("
                             (num "1")
                             ":"
                             [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                             ")")])))]
                       ":="
                       (Term.app `compl_singleton_mem_nhds [`zero_ne_one.symm]))))
                    []
                    (Mathlib.Tactic.«tacticUse_,,»
                     "use"
                     [(«term_∩_» `U "∩" `hatKstar) "," (Term.app `Filter.inter_mem [`U_in `this])])
                    []
                    (Tactic.constructor "constructor")
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Std.Tactic.rintro
                       "rintro"
                       [(Std.Tactic.RCases.rintroPat.one
                         (Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                            [])]
                          "⟩"))]
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                       [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                      []
                      (Tactic.exact "exact" (Term.app `h' [`rfl]))])
                    []
                    (tactic__
                     (cdotTk (patternIgnore (token.«· » "·")))
                     [(Std.Tactic.rintro
                       "rintro"
                       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                        (Std.Tactic.RCases.rintroPat.one
                         (Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                            [])]
                          "⟩"))
                        (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
                        (Std.Tactic.RCases.rintroPat.one
                         (Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                            [])]
                          "⟩"))]
                       [])
                      []
                      (Tactic.«tactic_<;>_»
                       (Tactic.apply "apply" `hU)
                       "<;>"
                       (Tactic.assumption "assumption"))])]))))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_in)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `zeroV')])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV')])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`nhds_right []]
                [(Term.typeSpec
                  ":"
                  («term_∈_»
                   (Set.Data.Set.Image.term_''_
                    (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_*_» `x "*" `x₀)))
                    " '' "
                    `V')
                   "∈"
                   (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`l []]
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `Function.LeftInverse
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             [(Term.typeSpec
                               ":"
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                             "=>"
                             («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             [(Term.typeSpec
                               ":"
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                             "=>"
                             («term_*_» `x "*" `x₀)))]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.intro "intro" [`x])
                           []
                           (Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `mul_assoc)
                              ","
                              (Tactic.simpLemma [] [] (Term.app `mul_inv_cancel [`h]))
                              ","
                              (Tactic.simpLemma [] [] `mul_one)]
                             "]"]
                            [])]))))))
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`r []]
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `Function.RightInverse
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             [(Term.typeSpec
                               ":"
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                             "=>"
                             («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                           (Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             [(Term.typeSpec
                               ":"
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                             "=>"
                             («term_*_» `x "*" `x₀)))]))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.intro "intro" [`x])
                           []
                           (Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `mul_assoc)
                              ","
                              (Tactic.simpLemma [] [] (Term.app `inv_mul_cancel [`h]))
                              ","
                              (Tactic.simpLemma [] [] `mul_one)]
                             "]"]
                            [])]))))))
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`c []]
                       [(Term.typeSpec
                         ":"
                         (Term.app
                          `Continuous
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [`x]
                             [(Term.typeSpec
                               ":"
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                             "=>"
                             («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))]))]
                       ":="
                       (Term.app `continuous_id.mul [`continuous_const]))))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `image_eq_preimage_of_inverse [`l `r]))]
                      "]")
                     [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule
                        [(patternIgnore (token.«← » "←"))]
                        (Term.app `mul_inv_cancel [`h]))]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`V'_in] []))])
                    []
                    (Tactic.exact "exact" (Term.app `c.continuous_at [`V'_in]))]))))))
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term∃_,_»
                   "∃"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z₀)] [":" `K]))
                   ","
                   (Std.ExtendedBinder.«term∃__,_»
                    "∃"
                    (Lean.binderIdent `y₀)
                    («binderTerm∈_» "∈" `V')
                    ","
                    («term_∧_»
                     («term_=_» (Term.app `coe [`z₀]) "=" («term_*_» `y₀ "*" `x₀))
                     "∧"
                     («term_≠_» `z₀ "≠" (num "0"))))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.rcases
                     "rcases"
                     [(Tactic.casesTarget
                       []
                       (Term.app `completion.dense_range_coe.mem_nhds [`nhds_right]))]
                     ["with"
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                            [":" («term_=_» («term_*_» `y₀ "*" `x₀) "=" `z₀)])]
                          "⟩")])
                       [])])
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.anonymousCtor
                      "⟨"
                      [`z₀
                       ","
                       `y₀
                       ","
                       `y₀_in
                       ","
                       (Term.anonymousCtor "⟨" [`H.symm "," (Term.hole "_")] "⟩")]
                      "⟩"))
                    []
                    (Std.Tactic.rintro
                     "rintro"
                     [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                     [])
                    []
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `mul_ne_zero
                      [(Term.app `ne_of_mem_of_not_mem [`y₀_in `zeroV']) `h `H]))]))))))
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `this)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz₀)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀_ne)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`vz₀_ne []]
                [(Term.typeSpec
                  ":"
                  («term_≠_»
                   (Term.typeAscription "(" (Term.app `v [`z₀]) ":" [`Γ₀] ")")
                   "≠"
                   (num "0")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Std.Tactic.tacticRwa__
                     "rwa"
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.ne_zero_iff)] "]")
                     [])]))))))
             []
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor "⟨" [(Term.app `v [`z₀]) "," (Term.hole "_")] "⟩"))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 []
                 (Term.app `LinearOrderedCommGroupWithZero.tendsto_of_ne_zero [`vz₀_ne]))
                ","
                (Tactic.rwRule [] `eventually_comap)]
               "]")
              [])
             []
             (Tactic.filterUpwards
              "filter_upwards"
              [(Tactic.termList "[" [`nhds_right] "]")]
              ["with" [`x `x_in `a `ha]]
              [])
             []
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] `x_in)]
              ["with"
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y_in)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                     [])]
                   "⟩")])
                [])])
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.typeAscription
                    "("
                    (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
                    ":"
                    [`Γ₀]
                    ")")
                   "="
                   (num "1")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.apply "apply" `hV)
                    []
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_=_»
                          (Term.typeAscription
                           "("
                           (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
                           ":"
                           [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                           ")")
                          "="
                          («term_⁻¹» `z₀ "⁻¹")))]
                       ":="
                       (Term.app
                        `map_inv₀
                        [(Term.typeAscription
                          "("
                          `completion.coe_ring_hom
                          ":"
                          [(Algebra.Hom.Ring.«term_→+*_»
                            `K
                            " →+* "
                            (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                          ")")
                         `z₀]))))
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `completion.coe_mul)
                       ","
                       (Tactic.rwRule [] `this)
                       ","
                       (Tactic.rwRule [] `ha)
                       ","
                       (Tactic.rwRule [] `hz₀)
                       ","
                       (Tactic.rwRule [] `mul_inv)
                       ","
                       (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
                       ","
                       (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                       ","
                       (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
                       ","
                       (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
                       ","
                       (Tactic.rwRule [] `mul_one)]
                      "]")
                     [])
                    []
                    (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])]))))))
             []
             (calcTactic
              "calc"
              (calcStep
               («term_=_»
                (Term.app `v [`a])
                "="
                (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)]))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `mul_assoc)
                      ","
                      (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
                      ","
                      (Tactic.rwRule [] `mul_one)]
                     "]")
                    [])]))))
              [(calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 («term_*_»
                  (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
                  "*"
                  (Term.app `v [`z₀])))
                ":="
                (Term.app `Valuation.map_mul [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
               (calcStep
                («term_=_» (Term.hole "_") "=" (Term.app `v [`z₀]))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)]
                      "]")
                     [])]))))])])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app `completion.dense_inducing_coe.continuous_extend [(Term.hole "_")]))
          []
          (Tactic.intro "intro" [`x₀])
          []
          (Std.Tactic.rcases
           "rcases"
           [(Tactic.casesTarget [] (Term.app `eq_or_ne [`x₀ (num "0")]))]
           ["with"
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.paren
                "("
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `rfl) "|" (Std.Tactic.RCases.rcasesPat.one `h)])
                 [])
                ")")])
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [(num "0") "," (Term.hole "_")] "⟩"))
            []
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                [(patternIgnore (token.«← » "←"))]
                `completion.dense_inducing_coe.to_inducing.nhds_eq_comap)]
              "]")
             [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `valued.continuous_valuation.tendsto'
              [(num "0") (num "0") (Term.app `map_zero [`v])]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`preimage_one []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  (Set.Data.Set.Image.«term_⁻¹'_»
                   `v
                   " ⁻¹' "
                   («term{_}» "{" [(Term.typeAscription "(" (num "1") ":" [`Γ₀] ")")] "}"))
                  "∈"
                  (Term.app
                   (TopologicalSpace.Topology.Basic.nhds "𝓝")
                   [(Term.typeAscription "(" (num "1") ":" [`K] ")")])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        («term_≠_»
                         (Term.typeAscription
                          "("
                          (Term.app `v [(Term.typeAscription "(" (num "1") ":" [`K] ")")])
                          ":"
                          [`Γ₀]
                          ")")
                         "≠"
                         (num "0")))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.map_one)] "]")
                           [])
                          []
                          (Tactic.exact "exact" `zero_ne_one.symm)]))))))
                   []
                   (convert "convert" [] (Term.app `Valued.loc_const [`this]) [])
                   []
                   (Std.Tactic.Ext.«tacticExt___:_»
                    "ext"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
                    [])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `Valuation.map_one)
                      ","
                      (Tactic.rwRule [] `mem_preimage)
                      ","
                      (Tactic.rwRule [] `mem_singleton_iff)
                      ","
                      (Tactic.rwRule [] `mem_set_of_eq)]
                     "]")
                    [])]))))))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_in)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV)])
                   [])]
                 "⟩")])]
             [":"
              (Std.ExtendedBinder.«term∃__,_»
               "∃"
               (Lean.binderIdent `V)
               («binderTerm∈_»
                "∈"
                (Term.app
                 (TopologicalSpace.Topology.Basic.nhds "𝓝")
                 [(Term.typeAscription
                   "("
                   (num "1")
                   ":"
                   [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                   ")")]))
               ","
               (Term.forall
                "∀"
                [`x]
                [(Term.typeSpec ":" `K)]
                ","
                (Term.arrow
                 («term_∈_»
                  (Term.typeAscription
                   "("
                   `x
                   ":"
                   [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                   ")")
                  "∈"
                  `V)
                 "→"
                 («term_=_»
                  (Term.typeAscription "(" (Term.app `v [`x]) ":" [`Γ₀] ")")
                  "="
                  (num "1")))))]
             [":="
              [(Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `completion.dense_inducing_coe.nhds_eq_comap)
                      ","
                      (Tactic.rwRule [] `mem_comap)]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`preimage_one] []))])])))]])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Std.ExtendedBinder.«term∃__,_»
                  "∃"
                  (Lean.binderIdent `V')
                  («binderTerm∈_»
                   "∈"
                   (Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.typeAscription
                      "("
                      (num "1")
                      ":"
                      [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                      ")")]))
                  ","
                  («term_∧_»
                   («term_∉_»
                    (Term.typeAscription
                     "("
                     (num "0")
                     ":"
                     [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                     ")")
                    "∉"
                    `V')
                   "∧"
                   (Term.forall
                    "∀"
                    [(Term.explicitBinder "(" [`x] [] [] ")")
                     (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `V')] [] ")")
                     (Term.explicitBinder "(" [`y] [] [] ")")
                     (Term.explicitBinder
                      "("
                      [(Term.hole "_")]
                      [":" («term_∈_» `y "∈" `V')]
                      []
                      ")")]
                    []
                    ","
                    («term_∈_» («term_*_» `x "*" («term_⁻¹» `y "⁻¹")) "∈" `V)))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        (Term.app
                         `tendsto
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`p]
                            [(Term.typeSpec
                              ":"
                              («term_×_»
                               (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                               "×"
                               (Term.app
                                (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                [`K])))]
                            "=>"
                            («term_*_»
                             (Term.proj `p "." (fieldIdx "1"))
                             "*"
                             («term_⁻¹» (Term.proj `p "." (fieldIdx "2")) "⁻¹"))))
                          (Term.app
                           (Term.proj
                            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])
                            "."
                            `Prod)
                           [(Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])])
                          (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])]))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                            "]")
                           [])
                          []
                          (Tactic.Conv.conv
                           "conv"
                           []
                           []
                           "=>"
                           (Tactic.Conv.convSeq
                            (Tactic.Conv.convSeq1Indented
                             [(Tactic.Conv.congr "congr")
                              []
                              (Tactic.Conv.skip "skip")
                              []
                              (Tactic.Conv.skip "skip")
                              []
                              (Tactic.Conv.convRw__
                               "rw"
                               []
                               (Tactic.rwRuleSeq
                                "["
                                [(Tactic.rwRule
                                  [(patternIgnore (token.«← » "←"))]
                                  (Term.app
                                   `one_mul
                                   [(Term.typeAscription
                                     "("
                                     (num "1")
                                     ":"
                                     [(Term.app
                                       (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                       [`K])]
                                     ")")]))]
                                "]"))])))
                          []
                          (Tactic.refine'
                           "refine'"
                           (Term.app
                            `tendsto.mul
                            [`continuous_fst.continuous_at
                             (Term.app
                              `tendsto.comp
                              [(Term.hole "_") `continuous_snd.continuous_at])]))
                          []
                          (convert
                           "convert"
                           []
                           (Term.app
                            `continuous_at_inv₀
                            [(Term.typeAscription
                              "("
                              `zero_ne_one.symm
                              ":"
                              [(«term_≠_»
                                (num "1")
                                "≠"
                                (Term.typeAscription
                                 "("
                                 (num "0")
                                 ":"
                                 [(Term.app
                                   (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                   [`K])]
                                 ")"))]
                              ")")])
                           [])
                          []
                          (Tactic.exact "exact" `inv_one.symm)]))))))
                   []
                   (Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget [] (Term.app `tendsto_prod_self_iff.mp [`this `V `V_in]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `U_in)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                           [])]
                         "⟩")])
                      [])])
                   []
                   (Tactic.tacticLet_
                    "let"
                    (Term.letDecl
                     (Term.letIdDecl
                      `hatKstar
                      []
                      []
                      ":="
                      (Term.typeAscription
                       "("
                       (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
                       ":"
                       [(«term_<|_»
                         `Set
                         "<|"
                         (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                       ")"))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        («term_∈_»
                         `hatKstar
                         "∈"
                         (Term.app
                          (TopologicalSpace.Topology.Basic.nhds "𝓝")
                          [(Term.typeAscription
                            "("
                            (num "1")
                            ":"
                            [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                            ")")])))]
                      ":="
                      (Term.app `compl_singleton_mem_nhds [`zero_ne_one.symm]))))
                   []
                   (Mathlib.Tactic.«tacticUse_,,»
                    "use"
                    [(«term_∩_» `U "∩" `hatKstar) "," (Term.app `Filter.inter_mem [`U_in `this])])
                   []
                   (Tactic.constructor "constructor")
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Std.Tactic.rintro
                      "rintro"
                      [(Std.Tactic.RCases.rintroPat.one
                        (Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                           [])]
                         "⟩"))]
                      [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                     []
                     (Tactic.exact "exact" (Term.app `h' [`rfl]))])
                   []
                   (tactic__
                    (cdotTk (patternIgnore (token.«· » "·")))
                    [(Std.Tactic.rintro
                      "rintro"
                      [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                       (Std.Tactic.RCases.rintroPat.one
                        (Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                           [])]
                         "⟩"))
                       (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
                       (Std.Tactic.RCases.rintroPat.one
                        (Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                           [])]
                         "⟩"))]
                      [])
                     []
                     (Tactic.«tactic_<;>_»
                      (Tactic.apply "apply" `hU)
                      "<;>"
                      (Tactic.assumption "assumption"))])]))))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_in)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `zeroV')])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV')])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`nhds_right []]
               [(Term.typeSpec
                 ":"
                 («term_∈_»
                  (Set.Data.Set.Image.term_''_
                   (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_*_» `x "*" `x₀)))
                   " '' "
                   `V')
                  "∈"
                  (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`l []]
                      [(Term.typeSpec
                        ":"
                        (Term.app
                         `Function.LeftInverse
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`x]
                            [(Term.typeSpec
                              ":"
                              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                            "=>"
                            («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`x]
                            [(Term.typeSpec
                              ":"
                              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                            "=>"
                            («term_*_» `x "*" `x₀)))]))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.intro "intro" [`x])
                          []
                          (Tactic.simp
                           "simp"
                           []
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `mul_assoc)
                             ","
                             (Tactic.simpLemma [] [] (Term.app `mul_inv_cancel [`h]))
                             ","
                             (Tactic.simpLemma [] [] `mul_one)]
                            "]"]
                           [])]))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`r []]
                      [(Term.typeSpec
                        ":"
                        (Term.app
                         `Function.RightInverse
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`x]
                            [(Term.typeSpec
                              ":"
                              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                            "=>"
                            («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                          (Term.fun
                           "fun"
                           (Term.basicFun
                            [`x]
                            [(Term.typeSpec
                              ":"
                              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                            "=>"
                            («term_*_» `x "*" `x₀)))]))]
                      ":="
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.intro "intro" [`x])
                          []
                          (Tactic.simp
                           "simp"
                           []
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `mul_assoc)
                             ","
                             (Tactic.simpLemma [] [] (Term.app `inv_mul_cancel [`h]))
                             ","
                             (Tactic.simpLemma [] [] `mul_one)]
                            "]"]
                           [])]))))))
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      [`c []]
                      [(Term.typeSpec
                        ":"
                        (Term.app
                         `Continuous
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`x]
                            [(Term.typeSpec
                              ":"
                              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                            "=>"
                            («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))]))]
                      ":="
                      (Term.app `continuous_id.mul [`continuous_const]))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] (Term.app `image_eq_preimage_of_inverse [`l `r]))]
                     "]")
                    [])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule
                       [(patternIgnore (token.«← » "←"))]
                       (Term.app `mul_inv_cancel [`h]))]
                     "]")
                    [(Tactic.location "at" (Tactic.locationHyp [`V'_in] []))])
                   []
                   (Tactic.exact "exact" (Term.app `c.continuous_at [`V'_in]))]))))))
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term∃_,_»
                  "∃"
                  (Lean.explicitBinders
                   (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z₀)] [":" `K]))
                  ","
                  (Std.ExtendedBinder.«term∃__,_»
                   "∃"
                   (Lean.binderIdent `y₀)
                   («binderTerm∈_» "∈" `V')
                   ","
                   («term_∧_»
                    («term_=_» (Term.app `coe [`z₀]) "=" («term_*_» `y₀ "*" `x₀))
                    "∧"
                    («term_≠_» `z₀ "≠" (num "0"))))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.rcases
                    "rcases"
                    [(Tactic.casesTarget
                      []
                      (Term.app `completion.dense_range_coe.mem_nhds [`nhds_right]))]
                    ["with"
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                           [":" («term_=_» («term_*_» `y₀ "*" `x₀) "=" `z₀)])]
                         "⟩")])
                      [])])
                   []
                   (Tactic.refine'
                    "refine'"
                    (Term.anonymousCtor
                     "⟨"
                     [`z₀
                      ","
                      `y₀
                      ","
                      `y₀_in
                      ","
                      (Term.anonymousCtor "⟨" [`H.symm "," (Term.hole "_")] "⟩")]
                     "⟩"))
                   []
                   (Std.Tactic.rintro
                    "rintro"
                    [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                    [])
                   []
                   (Tactic.exact
                    "exact"
                    (Term.app
                     `mul_ne_zero
                     [(Term.app `ne_of_mem_of_not_mem [`y₀_in `zeroV']) `h `H]))]))))))
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `this)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz₀)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀_ne)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`vz₀_ne []]
               [(Term.typeSpec
                 ":"
                 («term_≠_»
                  (Term.typeAscription "(" (Term.app `v [`z₀]) ":" [`Γ₀] ")")
                  "≠"
                  (num "0")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Std.Tactic.tacticRwa__
                    "rwa"
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.ne_zero_iff)] "]")
                    [])]))))))
            []
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor "⟨" [(Term.app `v [`z₀]) "," (Term.hole "_")] "⟩"))
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app `LinearOrderedCommGroupWithZero.tendsto_of_ne_zero [`vz₀_ne]))
               ","
               (Tactic.rwRule [] `eventually_comap)]
              "]")
             [])
            []
            (Tactic.filterUpwards
             "filter_upwards"
             [(Tactic.termList "[" [`nhds_right] "]")]
             ["with" [`x `x_in `a `ha]]
             [])
            []
            (Std.Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] `x_in)]
             ["with"
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y_in)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])])
            []
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Term.typeAscription
                   "("
                   (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
                   ":"
                   [`Γ₀]
                   ")")
                  "="
                  (num "1")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.apply "apply" `hV)
                   []
                   (Tactic.tacticHave_
                    "have"
                    (Term.haveDecl
                     (Term.haveIdDecl
                      []
                      [(Term.typeSpec
                        ":"
                        («term_=_»
                         (Term.typeAscription
                          "("
                          (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
                          ":"
                          [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                          ")")
                         "="
                         («term_⁻¹» `z₀ "⁻¹")))]
                      ":="
                      (Term.app
                       `map_inv₀
                       [(Term.typeAscription
                         "("
                         `completion.coe_ring_hom
                         ":"
                         [(Algebra.Hom.Ring.«term_→+*_»
                           `K
                           " →+* "
                           (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                         ")")
                        `z₀]))))
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `completion.coe_mul)
                      ","
                      (Tactic.rwRule [] `this)
                      ","
                      (Tactic.rwRule [] `ha)
                      ","
                      (Tactic.rwRule [] `hz₀)
                      ","
                      (Tactic.rwRule [] `mul_inv)
                      ","
                      (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
                      ","
                      (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                      ","
                      (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
                      ","
                      (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
                      ","
                      (Tactic.rwRule [] `mul_one)]
                     "]")
                    [])
                   []
                   (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])]))))))
            []
            (calcTactic
             "calc"
             (calcStep
              («term_=_»
               (Term.app `v [`a])
               "="
               (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `mul_assoc)
                     ","
                     (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
                     ","
                     (Tactic.rwRule [] `mul_one)]
                    "]")
                   [])]))))
             [(calcStep
               («term_=_»
                (Term.hole "_")
                "="
                («term_*_»
                 (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
                 "*"
                 (Term.app `v [`z₀])))
               ":="
               (Term.app `Valuation.map_mul [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
              (calcStep
               («term_=_» (Term.hole "_") "=" (Term.app `v [`z₀]))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)]
                     "]")
                    [])]))))])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`preimage_one []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              (Set.Data.Set.Image.«term_⁻¹'_»
               `v
               " ⁻¹' "
               («term{_}» "{" [(Term.typeAscription "(" (num "1") ":" [`Γ₀] ")")] "}"))
              "∈"
              (Term.app
               (TopologicalSpace.Topology.Basic.nhds "𝓝")
               [(Term.typeAscription "(" (num "1") ":" [`K] ")")])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_≠_»
                     (Term.typeAscription
                      "("
                      (Term.app `v [(Term.typeAscription "(" (num "1") ":" [`K] ")")])
                      ":"
                      [`Γ₀]
                      ")")
                     "≠"
                     (num "0")))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.map_one)] "]")
                       [])
                      []
                      (Tactic.exact "exact" `zero_ne_one.symm)]))))))
               []
               (convert "convert" [] (Term.app `Valued.loc_const [`this]) [])
               []
               (Std.Tactic.Ext.«tacticExt___:_»
                "ext"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Valuation.map_one)
                  ","
                  (Tactic.rwRule [] `mem_preimage)
                  ","
                  (Tactic.rwRule [] `mem_singleton_iff)
                  ","
                  (Tactic.rwRule [] `mem_set_of_eq)]
                 "]")
                [])]))))))
        []
        (Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V_in)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV)])
               [])]
             "⟩")])]
         [":"
          (Std.ExtendedBinder.«term∃__,_»
           "∃"
           (Lean.binderIdent `V)
           («binderTerm∈_»
            "∈"
            (Term.app
             (TopologicalSpace.Topology.Basic.nhds "𝓝")
             [(Term.typeAscription
               "("
               (num "1")
               ":"
               [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
               ")")]))
           ","
           (Term.forall
            "∀"
            [`x]
            [(Term.typeSpec ":" `K)]
            ","
            (Term.arrow
             («term_∈_»
              (Term.typeAscription
               "("
               `x
               ":"
               [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
               ")")
              "∈"
              `V)
             "→"
             («term_=_»
              (Term.typeAscription "(" (Term.app `v [`x]) ":" [`Γ₀] ")")
              "="
              (num "1")))))]
         [":="
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `completion.dense_inducing_coe.nhds_eq_comap)
                  ","
                  (Tactic.rwRule [] `mem_comap)]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`preimage_one] []))])])))]])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Std.ExtendedBinder.«term∃__,_»
              "∃"
              (Lean.binderIdent `V')
              («binderTerm∈_»
               "∈"
               (Term.app
                (TopologicalSpace.Topology.Basic.nhds "𝓝")
                [(Term.typeAscription
                  "("
                  (num "1")
                  ":"
                  [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                  ")")]))
              ","
              («term_∧_»
               («term_∉_»
                (Term.typeAscription
                 "("
                 (num "0")
                 ":"
                 [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                 ")")
                "∉"
                `V')
               "∧"
               (Term.forall
                "∀"
                [(Term.explicitBinder "(" [`x] [] [] ")")
                 (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `x "∈" `V')] [] ")")
                 (Term.explicitBinder "(" [`y] [] [] ")")
                 (Term.explicitBinder "(" [(Term.hole "_")] [":" («term_∈_» `y "∈" `V')] [] ")")]
                []
                ","
                («term_∈_» («term_*_» `x "*" («term_⁻¹» `y "⁻¹")) "∈" `V)))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `tendsto
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`p]
                        [(Term.typeSpec
                          ":"
                          («term_×_»
                           (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                           "×"
                           (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])))]
                        "=>"
                        («term_*_»
                         (Term.proj `p "." (fieldIdx "1"))
                         "*"
                         («term_⁻¹» (Term.proj `p "." (fieldIdx "2")) "⁻¹"))))
                      (Term.app
                       (Term.proj
                        (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])
                        "."
                        `Prod)
                       [(Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])])
                      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [(num "1")])]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `nhds_prod_eq)]
                        "]")
                       [])
                      []
                      (Tactic.Conv.conv
                       "conv"
                       []
                       []
                       "=>"
                       (Tactic.Conv.convSeq
                        (Tactic.Conv.convSeq1Indented
                         [(Tactic.Conv.congr "congr")
                          []
                          (Tactic.Conv.skip "skip")
                          []
                          (Tactic.Conv.skip "skip")
                          []
                          (Tactic.Conv.convRw__
                           "rw"
                           []
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule
                              [(patternIgnore (token.«← » "←"))]
                              (Term.app
                               `one_mul
                               [(Term.typeAscription
                                 "("
                                 (num "1")
                                 ":"
                                 [(Term.app
                                   (Valued.Topology.Algebra.ValuedField.termhat "hat")
                                   [`K])]
                                 ")")]))]
                            "]"))])))
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app
                        `tendsto.mul
                        [`continuous_fst.continuous_at
                         (Term.app `tendsto.comp [(Term.hole "_") `continuous_snd.continuous_at])]))
                      []
                      (convert
                       "convert"
                       []
                       (Term.app
                        `continuous_at_inv₀
                        [(Term.typeAscription
                          "("
                          `zero_ne_one.symm
                          ":"
                          [(«term_≠_»
                            (num "1")
                            "≠"
                            (Term.typeAscription
                             "("
                             (num "0")
                             ":"
                             [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                             ")"))]
                          ")")])
                       [])
                      []
                      (Tactic.exact "exact" `inv_one.symm)]))))))
               []
               (Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `tendsto_prod_self_iff.mp [`this `V `V_in]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U_in)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                       [])]
                     "⟩")])
                  [])])
               []
               (Tactic.tacticLet_
                "let"
                (Term.letDecl
                 (Term.letIdDecl
                  `hatKstar
                  []
                  []
                  ":="
                  (Term.typeAscription
                   "("
                   (Order.Basic.«term_ᶜ» («term{_}» "{" [(num "0")] "}") "ᶜ")
                   ":"
                   [(«term_<|_»
                     `Set
                     "<|"
                     (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                   ")"))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_∈_»
                     `hatKstar
                     "∈"
                     (Term.app
                      (TopologicalSpace.Topology.Basic.nhds "𝓝")
                      [(Term.typeAscription
                        "("
                        (num "1")
                        ":"
                        [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                        ")")])))]
                  ":="
                  (Term.app `compl_singleton_mem_nhds [`zero_ne_one.symm]))))
               []
               (Mathlib.Tactic.«tacticUse_,,»
                "use"
                [(«term_∩_» `U "∩" `hatKstar) "," (Term.app `Filter.inter_mem [`U_in `this])])
               []
               (Tactic.constructor "constructor")
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `h')])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_compl_singleton_iff)] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`h'] []))])
                 []
                 (Tactic.exact "exact" (Term.app `h' [`rfl]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Std.Tactic.rintro
                  "rintro"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])]
                     "⟩"))
                   (Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))
                   (Std.Tactic.RCases.rintroPat.one
                    (Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.ignore "_")])
                       [])]
                     "⟩"))]
                  [])
                 []
                 (Tactic.«tactic_<;>_»
                  (Tactic.apply "apply" `hU)
                  "<;>"
                  (Tactic.assumption "assumption"))])]))))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V')])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `V'_in)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `zeroV')])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hV')])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`nhds_right []]
           [(Term.typeSpec
             ":"
             («term_∈_»
              (Set.Data.Set.Image.term_''_
               (Term.fun "fun" (Term.basicFun [`x] [] "=>" («term_*_» `x "*" `x₀)))
               " '' "
               `V')
              "∈"
              (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x₀])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`l []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `Function.LeftInverse
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        "=>"
                        («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        "=>"
                        («term_*_» `x "*" `x₀)))]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.intro "intro" [`x])
                      []
                      (Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `mul_assoc)
                         ","
                         (Tactic.simpLemma [] [] (Term.app `mul_inv_cancel [`h]))
                         ","
                         (Tactic.simpLemma [] [] `mul_one)]
                        "]"]
                       [])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`r []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `Function.RightInverse
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        "=>"
                        («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        "=>"
                        («term_*_» `x "*" `x₀)))]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.intro "intro" [`x])
                      []
                      (Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `mul_assoc)
                         ","
                         (Tactic.simpLemma [] [] (Term.app `inv_mul_cancel [`h]))
                         ","
                         (Tactic.simpLemma [] [] `mul_one)]
                        "]"]
                       [])]))))))
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`c []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `Continuous
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`x]
                        [(Term.typeSpec
                          ":"
                          (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                        "=>"
                        («term_*_» `x "*" («term_⁻¹» `x₀ "⁻¹"))))]))]
                  ":="
                  (Term.app `continuous_id.mul [`continuous_const]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `image_eq_preimage_of_inverse [`l `r]))]
                 "]")
                [])
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app `mul_inv_cancel [`h]))]
                 "]")
                [(Tactic.location "at" (Tactic.locationHyp [`V'_in] []))])
               []
               (Tactic.exact "exact" (Term.app `c.continuous_at [`V'_in]))]))))))
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `z₀)] [":" `K]))
              ","
              (Std.ExtendedBinder.«term∃__,_»
               "∃"
               (Lean.binderIdent `y₀)
               («binderTerm∈_» "∈" `V')
               ","
               («term_∧_»
                («term_=_» (Term.app `coe [`z₀]) "=" («term_*_» `y₀ "*" `x₀))
                "∧"
                («term_≠_» `z₀ "≠" (num "0"))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.rcases
                "rcases"
                [(Tactic.casesTarget
                  []
                  (Term.app `completion.dense_range_coe.mem_nhds [`nhds_right]))]
                ["with"
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `H)])
                       [":" («term_=_» («term_*_» `y₀ "*" `x₀) "=" `z₀)])]
                     "⟩")])
                  [])])
               []
               (Tactic.refine'
                "refine'"
                (Term.anonymousCtor
                 "⟨"
                 [`z₀
                  ","
                  `y₀
                  ","
                  `y₀_in
                  ","
                  (Term.anonymousCtor "⟨" [`H.symm "," (Term.hole "_")] "⟩")]
                 "⟩"))
               []
               (Std.Tactic.rintro
                "rintro"
                [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `rfl))]
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 `mul_ne_zero
                 [(Term.app `ne_of_mem_of_not_mem [`y₀_in `zeroV']) `h `H]))]))))))
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `this)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y₀_in)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hz₀)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `z₀_ne)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`vz₀_ne []]
           [(Term.typeSpec
             ":"
             («term_≠_» (Term.typeAscription "(" (Term.app `v [`z₀]) ":" [`Γ₀] ")") "≠" (num "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Valuation.ne_zero_iff)] "]")
                [])]))))))
        []
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor "⟨" [(Term.app `v [`z₀]) "," (Term.hole "_")] "⟩"))
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            []
            (Term.app `LinearOrderedCommGroupWithZero.tendsto_of_ne_zero [`vz₀_ne]))
           ","
           (Tactic.rwRule [] `eventually_comap)]
          "]")
         [])
        []
        (Tactic.filterUpwards
         "filter_upwards"
         [(Tactic.termList "[" [`nhds_right] "]")]
         ["with" [`x `x_in `a `ha]]
         [])
        []
        (Std.Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] `x_in)]
         ["with"
          (Std.Tactic.RCases.rcasesPatLo
           (Std.Tactic.RCases.rcasesPatMed
            [(Std.Tactic.RCases.rcasesPat.tuple
              "⟨"
              [(Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y_in)])
                [])
               ","
               (Std.Tactic.RCases.rcasesPatLo
                (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                [])]
              "⟩")])
           [])])
        []
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.typeAscription
               "("
               (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
               ":"
               [`Γ₀]
               ")")
              "="
              (num "1")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.apply "apply" `hV)
               []
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_=_»
                     (Term.typeAscription
                      "("
                      (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
                      ":"
                      [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                      ")")
                     "="
                     («term_⁻¹» `z₀ "⁻¹")))]
                  ":="
                  (Term.app
                   `map_inv₀
                   [(Term.typeAscription
                     "("
                     `completion.coe_ring_hom
                     ":"
                     [(Algebra.Hom.Ring.«term_→+*_»
                       `K
                       " →+* "
                       (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                     ")")
                    `z₀]))))
               []
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `completion.coe_mul)
                  ","
                  (Tactic.rwRule [] `this)
                  ","
                  (Tactic.rwRule [] `ha)
                  ","
                  (Tactic.rwRule [] `hz₀)
                  ","
                  (Tactic.rwRule [] `mul_inv)
                  ","
                  (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
                  ","
                  (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                  ","
                  (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
                  ","
                  (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
                  ","
                  (Tactic.rwRule [] `mul_one)]
                 "]")
                [])
               []
               (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])]))))))
        []
        (calcTactic
         "calc"
         (calcStep
          («term_=_»
           (Term.app `v [`a])
           "="
           (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)]))
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `mul_assoc)
                 ","
                 (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
                 ","
                 (Tactic.rwRule [] `mul_one)]
                "]")
               [])]))))
         [(calcStep
           («term_=_»
            (Term.hole "_")
            "="
            («term_*_»
             (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
             "*"
             (Term.app `v [`z₀])))
           ":="
           (Term.app `Valuation.map_mul [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
          (calcStep
           («term_=_» (Term.hole "_") "=" (Term.app `v [`z₀]))
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)]
                 "]")
                [])]))))])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (calcTactic
       "calc"
       (calcStep
        («term_=_»
         (Term.app `v [`a])
         "="
         (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)]))
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `mul_assoc)
               ","
               (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
               ","
               (Tactic.rwRule [] `mul_one)]
              "]")
             [])]))))
       [(calcStep
         («term_=_»
          (Term.hole "_")
          "="
          («term_*_»
           (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
           "*"
           (Term.app `v [`z₀])))
         ":="
         (Term.app `Valuation.map_mul [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
        (calcStep
         («term_=_» (Term.hole "_") "=" (Term.app `v [`z₀]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)] "]")
              [])]))))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)] "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this) "," (Tactic.rwRule [] `one_mul)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `one_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.hole "_") "=" (Term.app `v [`z₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`z₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.app `Valuation.map_mul [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Valuation.map_mul
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.hole "_")
       "="
       («term_*_» (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))]) "*" (Term.app `v [`z₀])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))]) "*" (Term.app `v [`z₀]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`z₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `z₀ "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `mul_assoc)
             ","
             (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
             ","
             (Tactic.rwRule [] `mul_one)]
            "]")
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `mul_assoc)
         ","
         (Tactic.rwRule [] (Term.app `inv_mul_cancel [`z₀_ne]))
         ","
         (Tactic.rwRule [] `mul_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inv_mul_cancel [`z₀_ne])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z₀_ne
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inv_mul_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `v [`a])
       "="
       (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [(«term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `z₀ "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 70, (some 71, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_*_» («term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹")) "*" `z₀)
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `v [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.app `v [(«term_*_» `a "*" («term_⁻¹» `z₀ "⁻¹"))])
             ":"
             [`Γ₀]
             ")")
            "="
            (num "1")))]
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.apply "apply" `hV)
             []
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Term.typeAscription
                    "("
                    (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
                    ":"
                    [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                    ")")
                   "="
                   («term_⁻¹» `z₀ "⁻¹")))]
                ":="
                (Term.app
                 `map_inv₀
                 [(Term.typeAscription
                   "("
                   `completion.coe_ring_hom
                   ":"
                   [(Algebra.Hom.Ring.«term_→+*_»
                     `K
                     " →+* "
                     (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                   ")")
                  `z₀]))))
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `completion.coe_mul)
                ","
                (Tactic.rwRule [] `this)
                ","
                (Tactic.rwRule [] `ha)
                ","
                (Tactic.rwRule [] `hz₀)
                ","
                (Tactic.rwRule [] `mul_inv)
                ","
                (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
                ","
                (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
                ","
                (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
                ","
                (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
                ","
                (Tactic.rwRule [] `mul_one)]
               "]")
              [])
             []
             (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.apply "apply" `hV)
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.typeAscription
                 "("
                 (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
                 ":"
                 [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                 ")")
                "="
                («term_⁻¹» `z₀ "⁻¹")))]
             ":="
             (Term.app
              `map_inv₀
              [(Term.typeAscription
                "("
                `completion.coe_ring_hom
                ":"
                [(Algebra.Hom.Ring.«term_→+*_»
                  `K
                  " →+* "
                  (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
                ")")
               `z₀]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `completion.coe_mul)
             ","
             (Tactic.rwRule [] `this)
             ","
             (Tactic.rwRule [] `ha)
             ","
             (Tactic.rwRule [] `hz₀)
             ","
             (Tactic.rwRule [] `mul_inv)
             ","
             (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
             ","
             (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
             ","
             (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
             ","
             (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
             ","
             (Tactic.rwRule [] `mul_one)]
            "]")
           [])
          []
          (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.SolveByElim.solveByElim "solve_by_elim" [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `completion.coe_mul)
         ","
         (Tactic.rwRule [] `this)
         ","
         (Tactic.rwRule [] `ha)
         ","
         (Tactic.rwRule [] `hz₀)
         ","
         (Tactic.rwRule [] `mul_inv)
         ","
         (Tactic.rwRule [] (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")]))
         ","
         (Tactic.rwRule [(patternIgnore (token.«← » "←"))] `mul_assoc)
         ","
         (Tactic.rwRule [] (Term.app `mul_assoc [`y]))
         ","
         (Tactic.rwRule [] (Term.app `mul_inv_cancel [`h]))
         ","
         (Tactic.rwRule [] `mul_one)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_one
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_inv_cancel [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_inv_cancel
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_assoc [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_assoc
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mul_comm [(«term_⁻¹» `y₀ "⁻¹")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_⁻¹»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_⁻¹» `y₀ "⁻¹")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `y₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mul_comm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mul_inv
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hz₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `ha
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `completion.coe_mul
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         []
         [(Term.typeSpec
           ":"
           («term_=_»
            (Term.typeAscription
             "("
             (Term.typeAscription "(" («term_⁻¹» `z₀ "⁻¹") ":" [`K] ")")
             ":"
             [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
             ")")
            "="
            («term_⁻¹» `z₀ "⁻¹")))]
         ":="
         (Term.app
          `map_inv₀
          [(Term.typeAscription
            "("
            `completion.coe_ring_hom
            ":"
            [(Algebra.Hom.Ring.«term_→+*_»
              `K
              " →+* "
              (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
            ")")
           `z₀]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `map_inv₀
       [(Term.typeAscription
         "("
         `completion.coe_ring_hom
         ":"
         [(Algebra.Hom.Ring.«term_→+*_»
           `K
           " →+* "
           (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
         ")")
        `z₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `z₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.typeAscription
       "("
       `completion.coe_ring_hom
       ":"
       [(Algebra.Hom.Ring.«term_→+*_»
         `K
         " →+* "
         (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Hom.Ring.«term_→+*_»
       `K
       " →+* "
       (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
theorem
  continuous_extension
  : Continuous ( Valued.extension : hat K → Γ₀ )
  :=
    by
      refine' completion.dense_inducing_coe.continuous_extend _
        intro x₀
        rcases eq_or_ne x₀ 0 with ( rfl | h )
        ·
          refine' ⟨ 0 , _ ⟩
            erw [ ← completion.dense_inducing_coe.to_inducing.nhds_eq_comap ]
            exact valued.continuous_valuation.tendsto' 0 0 map_zero v
        ·
          have
              preimage_one
                : v ⁻¹' { ( 1 : Γ₀ ) } ∈ 𝓝 ( 1 : K )
                :=
                by
                  have
                      : ( v ( 1 : K ) : Γ₀ ) ≠ 0
                        :=
                        by rw [ Valuation.map_one ] exact zero_ne_one.symm
                    convert Valued.loc_const this
                    ext x
                    rw [ Valuation.map_one , mem_preimage , mem_singleton_iff , mem_set_of_eq ]
            obtain
              ⟨ V , V_in , hV ⟩
              : ∃ V ∈ 𝓝 ( 1 : hat K ) , ∀ x : K , ( x : hat K ) ∈ V → ( v x : Γ₀ ) = 1
              := by rwa [ completion.dense_inducing_coe.nhds_eq_comap , mem_comap ] at preimage_one
            have
              :
                  ∃
                    V'
                    ∈ 𝓝 ( 1 : hat K )
                    ,
                    ( 0 : hat K ) ∉ V' ∧ ∀ ( x ) ( _ : x ∈ V' ) ( y ) ( _ : y ∈ V' ) , x * y ⁻¹ ∈ V
                :=
                by
                  have
                      : tendsto fun p : hat K × hat K => p . 1 * p . 2 ⁻¹ 𝓝 1 . Prod 𝓝 1 𝓝 1
                        :=
                        by
                          rw [ ← nhds_prod_eq ]
                            conv => congr skip skip rw [ ← one_mul ( 1 : hat K ) ]
                            refine'
                              tendsto.mul
                                continuous_fst.continuous_at
                                  tendsto.comp _ continuous_snd.continuous_at
                            convert continuous_at_inv₀ ( zero_ne_one.symm : 1 ≠ ( 0 : hat K ) )
                            exact inv_one.symm
                    rcases tendsto_prod_self_iff.mp this V V_in with ⟨ U , U_in , hU ⟩
                    let hatKstar := ( { 0 } ᶜ : Set <| hat K )
                    have : hatKstar ∈ 𝓝 ( 1 : hat K ) := compl_singleton_mem_nhds zero_ne_one.symm
                    use U ∩ hatKstar , Filter.inter_mem U_in this
                    constructor
                    · rintro ⟨ h , h' ⟩ rw [ mem_compl_singleton_iff ] at h' exact h' rfl
                    · rintro x ⟨ hx , _ ⟩ y ⟨ hy , _ ⟩ apply hU <;> assumption
            rcases this with ⟨ V' , V'_in , zeroV' , hV' ⟩
            have
              nhds_right
                : fun x => x * x₀ '' V' ∈ 𝓝 x₀
                :=
                by
                  have
                      l
                        : Function.LeftInverse fun x : hat K => x * x₀ ⁻¹ fun x : hat K => x * x₀
                        :=
                        by intro x simp only [ mul_assoc , mul_inv_cancel h , mul_one ]
                    have
                      r
                        : Function.RightInverse fun x : hat K => x * x₀ ⁻¹ fun x : hat K => x * x₀
                        :=
                        by intro x simp only [ mul_assoc , inv_mul_cancel h , mul_one ]
                    have
                      c
                        : Continuous fun x : hat K => x * x₀ ⁻¹
                        :=
                        continuous_id.mul continuous_const
                    rw [ image_eq_preimage_of_inverse l r ]
                    rw [ ← mul_inv_cancel h ] at V'_in
                    exact c.continuous_at V'_in
            have
              : ∃ z₀ : K , ∃ y₀ ∈ V' , coe z₀ = y₀ * x₀ ∧ z₀ ≠ 0
                :=
                by
                  rcases
                      completion.dense_range_coe.mem_nhds nhds_right
                      with ⟨ z₀ , y₀ , y₀_in , H : y₀ * x₀ = z₀ ⟩
                    refine' ⟨ z₀ , y₀ , y₀_in , ⟨ H.symm , _ ⟩ ⟩
                    rintro rfl
                    exact mul_ne_zero ne_of_mem_of_not_mem y₀_in zeroV' h H
            rcases this with ⟨ z₀ , y₀ , y₀_in , hz₀ , z₀_ne ⟩
            have vz₀_ne : ( v z₀ : Γ₀ ) ≠ 0 := by rwa [ Valuation.ne_zero_iff ]
            refine' ⟨ v z₀ , _ ⟩
            rw [ LinearOrderedCommGroupWithZero.tendsto_of_ne_zero vz₀_ne , eventually_comap ]
            filter_upwards [ nhds_right ] with x x_in a ha
            rcases x_in with ⟨ y , y_in , rfl ⟩
            have
              : ( v a * z₀ ⁻¹ : Γ₀ ) = 1
                :=
                by
                  apply hV
                    have
                      : ( ( z₀ ⁻¹ : K ) : hat K ) = z₀ ⁻¹
                        :=
                        map_inv₀ ( completion.coe_ring_hom : K →+* hat K ) z₀
                    rw
                      [
                        completion.coe_mul
                          ,
                          this
                          ,
                          ha
                          ,
                          hz₀
                          ,
                          mul_inv
                          ,
                          mul_comm y₀ ⁻¹
                          ,
                          ← mul_assoc
                          ,
                          mul_assoc y
                          ,
                          mul_inv_cancel h
                          ,
                          mul_one
                        ]
                    solve_by_elim
            calc
              v a = v a * z₀ ⁻¹ * z₀ := by rw [ mul_assoc , inv_mul_cancel z₀_ne , mul_one ]
              _ = v a * z₀ ⁻¹ * v z₀ := Valuation.map_mul _ _ _ _ = v z₀ := by rw [ this , one_mul ]
#align valued.continuous_extension Valued.continuous_extension

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      []
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simp "simp" [] []))
         ","
         (Term.attrInstance
          (Term.attrKind [])
          (Std.Tactic.NormCast.Attr.norm_cast "norm_cast" [] []))]
        "]")]
      []
      []
      []
      [])
     (Command.theorem
      "theorem"
      (Command.declId `extension_extends [])
      (Command.declSig
       [(Term.explicitBinder "(" [`x] [":" `K] [] ")")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `extension
          [(Term.typeAscription
            "("
            `x
            ":"
            [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
            ")")])
         "="
         (Term.app `v [`x]))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.refine'
            "refine'"
            (Term.app `completion.dense_inducing_coe.extend_eq_of_tendsto [(Term.hole "_")]))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               [(patternIgnore (token.«← » "←"))]
               `completion.dense_inducing_coe.nhds_eq_comap)]
             "]")
            [])
           []
           (Tactic.exact "exact" `valued.continuous_valuation.continuous_at)])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.refine'
           "refine'"
           (Term.app `completion.dense_inducing_coe.extend_eq_of_tendsto [(Term.hole "_")]))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              [(patternIgnore (token.«← » "←"))]
              `completion.dense_inducing_coe.nhds_eq_comap)]
            "]")
           [])
          []
          (Tactic.exact "exact" `valued.continuous_valuation.continuous_at)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `valued.continuous_valuation.continuous_at)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `valued.continuous_valuation.continuous_at
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule
          [(patternIgnore (token.«← » "←"))]
          `completion.dense_inducing_coe.nhds_eq_comap)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `completion.dense_inducing_coe.nhds_eq_comap
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app `completion.dense_inducing_coe.extend_eq_of_tendsto [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `completion.dense_inducing_coe.extend_eq_of_tendsto [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `completion.dense_inducing_coe.extend_eq_of_tendsto
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `extension
        [(Term.typeAscription
          "("
          `x
          ":"
          [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
          ")")])
       "="
       (Term.app `v [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `extension
       [(Term.typeAscription
         "("
         `x
         ":"
         [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `x
       ":"
       [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
@[ simp , norm_cast ]
  theorem
    extension_extends
    ( x : K ) : extension ( x : hat K ) = v x
    :=
      by
        refine' completion.dense_inducing_coe.extend_eq_of_tendsto _
          rw [ ← completion.dense_inducing_coe.nhds_eq_comap ]
          exact valued.continuous_valuation.continuous_at
#align valued.extension_extends Valued.extension_extends

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "the extension of a valuation on a division ring to its completion. -/")]
      []
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `extensionValuation [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (Term.app
          `Valuation
          [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) `Γ₀]))])
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl (Term.letIdDecl `toFun [] [] ":=" `Valued.extension)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_zero'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `v.map_zero)
                  ","
                  (Tactic.rwRule
                   [(patternIgnore (token.«← » "←"))]
                   (Term.app
                    `Valued.extension_extends
                    [(Term.typeAscription "(" (num "0") ":" [`K] ")")]))]
                 "]")
                [])
               []
               (Tactic.tacticRfl "rfl")]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_one'
           []
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `completion.coe_one)
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `Valued.extension_extends
                    [(Term.typeAscription "(" (num "1") ":" [`K] ")")]))]
                 "]")
                [])
               []
               (Tactic.exact "exact" (Term.app `Valuation.map_one [(Term.hole "_")]))]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_mul'
           [`x `y]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.apply "apply" (Term.app `completion.induction_on₂ [`x `y]))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`c1 []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `Continuous
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`x]
                          [(Term.typeSpec
                            ":"
                            («term_×_»
                             (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                             "×"
                             (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])))]
                          "=>"
                          (Term.app
                           `Valued.extension
                           [(«term_*_»
                             (Term.proj `x "." (fieldIdx "1"))
                             "*"
                             (Term.proj `x "." (fieldIdx "2")))])))]))]
                    ":="
                    (Term.app
                     `valued.continuous_extension.comp
                     [(Term.app `continuous_fst.mul [`continuous_snd])]))))
                 []
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`c2 []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `Continuous
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`x]
                          [(Term.typeSpec
                            ":"
                            («term_×_»
                             (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                             "×"
                             (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])))]
                          "=>"
                          («term_*_»
                           (Term.app `Valued.extension [(Term.proj `x "." (fieldIdx "1"))])
                           "*"
                           (Term.app `Valued.extension [(Term.proj `x "." (fieldIdx "2"))]))))]))]
                    ":="
                    (Term.app
                     (Term.proj
                      (Term.app `valued.continuous_extension.comp [`continuous_fst])
                      "."
                      `mul)
                     [(Term.app `valued.continuous_extension.comp [`continuous_snd])]))))
                 []
                 (Tactic.exact "exact" (Term.app `is_closed_eq [`c1 `c2]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" [`x `y])
                 []
                 (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   `Valuation.map_mul
                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))])]))))))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `map_add_le_max'
           [`x `y]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_max_iff)] "]") [])
               []
               (Tactic.apply "apply" (Term.app `completion.induction_on₂ [`x `y]))
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`cont []]
                    [(Term.typeSpec
                      ":"
                      (Term.app
                       `Continuous
                       [(Term.typeAscription
                         "("
                         `Valued.extension
                         ":"
                         [(Term.arrow
                           (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                           "→"
                           `Γ₀)]
                         ")")]))]
                    ":="
                    `Valued.continuous_extension)))
                 []
                 (Tactic.exact
                  "exact"
                  (Term.app
                   (Term.proj
                    («term_<|_»
                     (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
                     "<|"
                     (Term.app `cont.comp [`continuous_fst]))
                    "."
                    `union)
                   [(«term_<|_»
                     (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
                     "<|"
                     (Term.app `cont.comp [`continuous_snd]))]))])
               []
               (tactic__
                (cdotTk (patternIgnore (token.«· » "·")))
                [(Tactic.intro "intro" [`x `y])
                 []
                 (Tactic.dsimp "dsimp" [] [] [] [] [])
                 []
                 (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `le_max_iff)]
                   "]")
                  [])
                 []
                 (Tactic.exact "exact" (Term.app `v.map_add [`x `y]))])]))))))]
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `le_max_iff)] "]") [])
          []
          (Tactic.apply "apply" (Term.app `completion.induction_on₂ [`x `y]))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`cont []]
               [(Term.typeSpec
                 ":"
                 (Term.app
                  `Continuous
                  [(Term.typeAscription
                    "("
                    `Valued.extension
                    ":"
                    [(Term.arrow
                      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                      "→"
                      `Γ₀)]
                    ")")]))]
               ":="
               `Valued.continuous_extension)))
            []
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               («term_<|_»
                (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
                "<|"
                (Term.app `cont.comp [`continuous_fst]))
               "."
               `union)
              [(«term_<|_»
                (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
                "<|"
                (Term.app `cont.comp [`continuous_snd]))]))])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Tactic.intro "intro" [`x `y])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `le_max_iff)]
              "]")
             [])
            []
            (Tactic.exact "exact" (Term.app `v.map_add [`x `y]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.intro "intro" [`x `y])
        []
        (Tactic.dsimp "dsimp" [] [] [] [] [])
        []
        (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `le_max_iff)] "]")
         [])
        []
        (Tactic.exact "exact" (Term.app `v.map_add [`x `y]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `v.map_add [`x `y]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `v.map_add [`x `y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v.map_add
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `le_max_iff)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `le_max_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.NormCast.tacticNorm_cast__ "norm_cast" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`x `y])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`cont []]
           [(Term.typeSpec
             ":"
             (Term.app
              `Continuous
              [(Term.typeAscription
                "("
                `Valued.extension
                ":"
                [(Term.arrow
                  (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                  "→"
                  `Γ₀)]
                ")")]))]
           ":="
           `Valued.continuous_extension)))
        []
        (Tactic.exact
         "exact"
         (Term.app
          (Term.proj
           («term_<|_»
            (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
            "<|"
            (Term.app `cont.comp [`continuous_fst]))
           "."
           `union)
          [(«term_<|_»
            (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
            "<|"
            (Term.app `cont.comp [`continuous_snd]))]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj
         («term_<|_»
          (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
          "<|"
          (Term.app `cont.comp [`continuous_fst]))
         "."
         `union)
        [(«term_<|_»
          (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
          "<|"
          (Term.app `cont.comp [`continuous_snd]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj
        («term_<|_»
         (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
         "<|"
         (Term.app `cont.comp [`continuous_fst]))
        "."
        `union)
       [(«term_<|_»
         (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
         "<|"
         (Term.app `cont.comp [`continuous_snd]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<|_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
       "<|"
       (Term.app `cont.comp [`continuous_snd]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cont.comp [`continuous_snd])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_snd
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cont.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cont.comp [`continuous_add])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_add
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cont.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cont.comp [`continuous_add])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_closed_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `is_closed_le [(Term.paren "(" (Term.app `cont.comp [`continuous_add]) ")")])
      "<|"
      (Term.app `cont.comp [`continuous_snd]))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj
       («term_<|_»
        (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
        "<|"
        (Term.app `cont.comp [`continuous_fst]))
       "."
       `union)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      («term_<|_»
       (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
       "<|"
       (Term.app `cont.comp [`continuous_fst]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cont.comp [`continuous_fst])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_fst
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cont.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `is_closed_le [(Term.app `cont.comp [`continuous_add])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `cont.comp [`continuous_add])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `continuous_add
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `cont.comp
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `cont.comp [`continuous_add])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `is_closed_le
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_<|_»
      (Term.app `is_closed_le [(Term.paren "(" (Term.app `cont.comp [`continuous_add]) ")")])
      "<|"
      (Term.app `cont.comp [`continuous_fst]))
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`cont []]
         [(Term.typeSpec
           ":"
           (Term.app
            `Continuous
            [(Term.typeAscription
              "("
              `Valued.extension
              ":"
              [(Term.arrow
                (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
                "→"
                `Γ₀)]
              ")")]))]
         ":="
         `Valued.continuous_extension)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Valued.continuous_extension
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Continuous
       [(Term.typeAscription
         "("
         `Valued.extension
         ":"
         [(Term.arrow (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) "→" `Γ₀)]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       `Valued.extension
       ":"
       [(Term.arrow (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) "→" `Γ₀)]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.arrow (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) "→" `Γ₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 25 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- the extension of a valuation on a division ring to its completion. -/ noncomputable
  def
    extensionValuation
    : Valuation hat K Γ₀
    where
      toFun := Valued.extension
        map_zero' := by rw [ ← v.map_zero , ← Valued.extension_extends ( 0 : K ) ] rfl
        map_one'
          :=
          by
            rw [ ← completion.coe_one , Valued.extension_extends ( 1 : K ) ]
              exact Valuation.map_one _
        map_mul'
          x y
          :=
          by
            apply completion.induction_on₂ x y
              ·
                have
                    c1
                      : Continuous fun x : hat K × hat K => Valued.extension x . 1 * x . 2
                      :=
                      valued.continuous_extension.comp continuous_fst.mul continuous_snd
                  have
                    c2
                      :
                        Continuous
                          fun x : hat K × hat K => Valued.extension x . 1 * Valued.extension x . 2
                      :=
                      valued.continuous_extension.comp continuous_fst . mul
                        valued.continuous_extension.comp continuous_snd
                  exact is_closed_eq c1 c2
              · intro x y norm_cast exact Valuation.map_mul _ _ _
        map_add_le_max'
          x y
          :=
          by
            rw [ le_max_iff ]
              apply completion.induction_on₂ x y
              ·
                have
                    cont
                      : Continuous ( Valued.extension : hat K → Γ₀ )
                      :=
                      Valued.continuous_extension
                  exact
                    is_closed_le cont.comp continuous_add <| cont.comp continuous_fst . union
                      is_closed_le cont.comp continuous_add <| cont.comp continuous_snd
              · intro x y dsimp norm_cast rw [ ← le_max_iff ] exact v.map_add x y
#align valued.extension_valuation Valued.extensionValuation

/- failed to parenthesize: unknown constant 'group'
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `closure_coe_completion_v_lt [])
      (Command.declSig
       [(Term.implicitBinder "{" [`γ] [":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ")] "}")]
       (Term.typeSpec
        ":"
        («term_=_»
         (Term.app
          `closure
          [(Set.Data.Set.Image.term_''_
            `coe
            " '' "
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
             "|"
             («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
             "}"))])
         "="
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder
           (Lean.binderIdent `x)
           [(group ":" (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))])
          "|"
          («term_<_»
           (Term.app `extensionValuation [`x])
           "<"
           (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
          "}"))))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Std.Tactic.Ext.«tacticExt___:_»
            "ext"
            [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
            [])
           []
           (Tactic.tacticLet_
            "let"
            (Term.letDecl (Term.letIdDecl `γ₀ [] [] ":=" (Term.app `extension_valuation [`x]))))
           []
           (Tactic.tacticSuffices_
            "suffices"
            (Term.sufficesDecl
             []
             (Term.arrow
              («term_≠_» `γ₀ "≠" (num "0"))
              "→"
              («term_↔_»
               («term_∈_»
                `x
                "∈"
                (Term.app
                 `closure
                 [(Set.Data.Set.Image.term_''_
                   `coe
                   " '' "
                   (Set.«term{_|_}»
                    "{"
                    (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
                    "|"
                    («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
                    "}"))]))
               "↔"
               («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))))
             (Term.byTactic'
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.cases
                  "cases"
                  [(Tactic.casesTarget [] (Term.app `eq_or_ne [`γ₀ (num "0")]))]
                  []
                  [])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `h)
                      ","
                      (Tactic.simpLemma
                       []
                       []
                       (Term.app
                        (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp)
                        [`h]))
                      ","
                      (Tactic.simpLemma [] [] `mem_set_of_eq)
                      ","
                      (Tactic.simpLemma [] [] `Valuation.map_zero)
                      ","
                      (Tactic.simpLemma [] [] `Units.zero_lt)
                      ","
                      (Tactic.simpLemma [] [] `iff_true_iff)]
                     "]"]
                    [])
                   []
                   (Tactic.apply "apply" `subset_closure)
                   []
                   (Tactic.exact
                    "exact"
                    (Term.anonymousCtor
                     "⟨"
                     [(num "0")
                      ","
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Std.Tactic.Simpa.simpa
                           "simpa"
                           []
                           []
                           (Std.Tactic.Simpa.simpaArgsRest
                            []
                            []
                            ["only"]
                            [(Tactic.simpArgs
                              "["
                              [(Tactic.simpLemma [] [] `mem_set_of_eq)
                               ","
                               (Tactic.simpLemma [] [] `Valuation.map_zero)
                               ","
                               (Tactic.simpLemma [] [] `Units.zero_lt)
                               ","
                               (Tactic.simpLemma [] [] `true_and_iff)]
                              "]")]
                            []))])))]
                     "⟩"))])
                 []
                 (tactic__
                  (cdotTk (patternIgnore (token.«· » "·")))
                  [(Tactic.exact "exact" (Term.app `this [`h]))])])))))
           []
           (Tactic.intro "intro" [`h])
           []
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`hγ₀ []]
              [(Term.typeSpec
                ":"
                («term_∈_»
                 (Set.Data.Set.Image.«term_⁻¹'_» `extension " ⁻¹' " («term{_}» "{" [`γ₀] "}"))
                 "∈"
                 (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
              ":="
              (Term.app
               `continuous_extension.continuous_at.preimage_mem_nhds
               [(Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])]))))
           []
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_closure_iff_nhds')] "]")
            [])
           []
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [`hx] [] "=>" (Term.hole "_")))
              ","
              (Term.fun "fun" (Term.basicFun [`hx `s `hs] [] "=>" (Term.hole "_")))]
             "⟩"))
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                         [":"
                          («term_<_»
                           (Term.app `v [`y])
                           "<"
                           (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                         [])]
                       "⟩")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
                    [])]
                  "⟩")])]
              []
              [":=" [(Term.app `hx [(Term.hole "_") `hγ₀])]])
             []
             (Mathlib.Tactic.replace'
              "replace"
              [`hy₂ []]
              [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₂]))])
             []
             (Std.Tactic.tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₂)] "]")
              [])])
           []
           (tactic__
            (cdotTk (patternIgnore (token.«· » "·")))
            [(Std.Tactic.obtain
              "obtain"
              [(Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
                    [":" («term_∈_» (coeNotation "↑" `y) "∈" `s)])]
                  "⟩")])]
              []
              [":="
               [(Term.app
                 `completion.dense_range_coe.mem_nhds
                 [(Term.app `inter_mem [`hγ₀ `hs])])]])
             []
             (Mathlib.Tactic.replace'
              "replace"
              [`hy₁ []]
              [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
             []
             (tactic__
              (cdotTk (patternIgnore (token.«· » "·")))
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₁]))])
             []
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₁)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
             []
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.anonymousCtor
                 "⟨"
                 [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")]
                 "⟩")
                ","
                `hy₂]
               "⟩"))])])))
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
           [])
          []
          (Tactic.tacticLet_
           "let"
           (Term.letDecl (Term.letIdDecl `γ₀ [] [] ":=" (Term.app `extension_valuation [`x]))))
          []
          (Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.arrow
             («term_≠_» `γ₀ "≠" (num "0"))
             "→"
             («term_↔_»
              («term_∈_»
               `x
               "∈"
               (Term.app
                `closure
                [(Set.Data.Set.Image.term_''_
                  `coe
                  " '' "
                  (Set.«term{_|_}»
                   "{"
                   (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
                   "|"
                   («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
                   "}"))]))
              "↔"
              («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))))
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.cases
                 "cases"
                 [(Tactic.casesTarget [] (Term.app `eq_or_ne [`γ₀ (num "0")]))]
                 []
                 [])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.simp
                   "simp"
                   []
                   []
                   ["only"]
                   ["["
                    [(Tactic.simpLemma [] [] `h)
                     ","
                     (Tactic.simpLemma
                      []
                      []
                      (Term.app
                       (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp)
                       [`h]))
                     ","
                     (Tactic.simpLemma [] [] `mem_set_of_eq)
                     ","
                     (Tactic.simpLemma [] [] `Valuation.map_zero)
                     ","
                     (Tactic.simpLemma [] [] `Units.zero_lt)
                     ","
                     (Tactic.simpLemma [] [] `iff_true_iff)]
                    "]"]
                   [])
                  []
                  (Tactic.apply "apply" `subset_closure)
                  []
                  (Tactic.exact
                   "exact"
                   (Term.anonymousCtor
                    "⟨"
                    [(num "0")
                     ","
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Std.Tactic.Simpa.simpa
                          "simpa"
                          []
                          []
                          (Std.Tactic.Simpa.simpaArgsRest
                           []
                           []
                           ["only"]
                           [(Tactic.simpArgs
                             "["
                             [(Tactic.simpLemma [] [] `mem_set_of_eq)
                              ","
                              (Tactic.simpLemma [] [] `Valuation.map_zero)
                              ","
                              (Tactic.simpLemma [] [] `Units.zero_lt)
                              ","
                              (Tactic.simpLemma [] [] `true_and_iff)]
                             "]")]
                           []))])))]
                    "⟩"))])
                []
                (tactic__
                 (cdotTk (patternIgnore (token.«· » "·")))
                 [(Tactic.exact "exact" (Term.app `this [`h]))])])))))
          []
          (Tactic.intro "intro" [`h])
          []
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hγ₀ []]
             [(Term.typeSpec
               ":"
               («term_∈_»
                (Set.Data.Set.Image.«term_⁻¹'_» `extension " ⁻¹' " («term{_}» "{" [`γ₀] "}"))
                "∈"
                (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
             ":="
             (Term.app
              `continuous_extension.continuous_at.preimage_mem_nhds
              [(Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])]))))
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_closure_iff_nhds')] "]")
           [])
          []
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.fun "fun" (Term.basicFun [`hx] [] "=>" (Term.hole "_")))
             ","
             (Term.fun "fun" (Term.basicFun [`hx `s `hs] [] "=>" (Term.hole "_")))]
            "⟩"))
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                        [":"
                         («term_<_»
                          (Term.app `v [`y])
                          "<"
                          (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                        [])]
                      "⟩")])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
                   [])]
                 "⟩")])]
             []
             [":=" [(Term.app `hx [(Term.hole "_") `hγ₀])]])
            []
            (Mathlib.Tactic.replace'
             "replace"
             [`hy₂ []]
             [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₂]))])
            []
            (Std.Tactic.tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₂)] "]")
             [])])
          []
          (tactic__
           (cdotTk (patternIgnore (token.«· » "·")))
           [(Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
                   [":" («term_∈_» (coeNotation "↑" `y) "∈" `s)])]
                 "⟩")])]
             []
             [":="
              [(Term.app `completion.dense_range_coe.mem_nhds [(Term.app `inter_mem [`hγ₀ `hs])])]])
            []
            (Mathlib.Tactic.replace'
             "replace"
             [`hy₁ []]
             [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Std.Tactic.Simpa.simpa
               "simpa"
               []
               []
               (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₁]))])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₁)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            []
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.anonymousCtor
                "⟨"
                [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")]
                "⟩")
               ","
               `hy₂]
              "⟩"))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
               [":" («term_∈_» (coeNotation "↑" `y) "∈" `s)])]
             "⟩")])]
         []
         [":="
          [(Term.app `completion.dense_range_coe.mem_nhds [(Term.app `inter_mem [`hγ₀ `hs])])]])
        []
        (Mathlib.Tactic.replace'
         "replace"
         [`hy₁ []]
         [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₁]))])
        []
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₁)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")] "⟩")
           ","
           `hy₂]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(Term.anonymousCtor "⟨" [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")] "⟩")
         ","
         `hy₂]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.anonymousCtor "⟨" [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")] "⟩")
        ","
        `hy₂]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`y "," (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`y "," `hx "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₁)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₁]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₁]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₁
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`hy₁ []]
       [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `v [`y]) "=" `γ₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `v [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
             [":" («term_∈_» (coeNotation "↑" `y) "∈" `s)])]
           "⟩")])]
       []
       [":=" [(Term.app `completion.dense_range_coe.mem_nhds [(Term.app `inter_mem [`hγ₀ `hs])])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `completion.dense_range_coe.mem_nhds [(Term.app `inter_mem [`hγ₀ `hs])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `inter_mem [`hγ₀ `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hγ₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `inter_mem
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `inter_mem [`hγ₀ `hs]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `completion.dense_range_coe.mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» (coeNotation "↑" `y) "∈" `s)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (coeNotation "↑" `y)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (some 1024, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.obtain
         "obtain"
         [(Std.Tactic.RCases.rcasesPatMed
           [(Std.Tactic.RCases.rcasesPat.tuple
             "⟨"
             [(Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed
                [(Std.Tactic.RCases.rcasesPat.tuple
                  "⟨"
                  [(Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                    [])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                    [":"
                     («term_<_» (Term.app `v [`y]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))])
                   ","
                   (Std.Tactic.RCases.rcasesPatLo
                    (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                    [])]
                  "⟩")])
               [])
              ","
              (Std.Tactic.RCases.rcasesPatLo
               (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
               [])]
             "⟩")])]
         []
         [":=" [(Term.app `hx [(Term.hole "_") `hγ₀])]])
        []
        (Mathlib.Tactic.replace'
         "replace"
         [`hy₂ []]
         [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
        []
        (tactic__
         (cdotTk (patternIgnore (token.«· » "·")))
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₂]))])
        []
        (Std.Tactic.tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₂)] "]")
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.tacticRwa__
       "rwa"
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `hy₂)] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Std.Tactic.Simpa.simpa
         "simpa"
         []
         []
         (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₂]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest [] [] [] [] ["using" `hy₂]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hy₂
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.replace'
       "replace"
       [`hy₂ []]
       [(Term.typeSpec ":" («term_=_» (Term.app `v [`y]) "=" `γ₀))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `v [`y]) "=" `γ₀)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `v [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.tuple
                "⟨"
                [(Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.clear "-")])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `y)])
                  [])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₁)])
                  [":"
                   («term_<_» (Term.app `v [`y]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))])
                 ","
                 (Std.Tactic.RCases.rcasesPatLo
                  (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `rfl)])
                  [])]
                "⟩")])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hy₂)])
             [])]
           "⟩")])]
       []
       [":=" [(Term.app `hx [(Term.hole "_") `hγ₀])]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `hx [(Term.hole "_") `hγ₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hγ₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `v [`y]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `γ ":" [`Γ₀] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `v [`y])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.anonymousCtor
        "⟨"
        [(Term.fun "fun" (Term.basicFun [`hx] [] "=>" (Term.hole "_")))
         ","
         (Term.fun "fun" (Term.basicFun [`hx `s `hs] [] "=>" (Term.hole "_")))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.fun "fun" (Term.basicFun [`hx] [] "=>" (Term.hole "_")))
        ","
        (Term.fun "fun" (Term.basicFun [`hx `s `hs] [] "=>" (Term.hole "_")))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`hx `s `hs] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hs
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`hx] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_closure_iff_nhds')] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_closure_iff_nhds'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticHave_
       "have"
       (Term.haveDecl
        (Term.haveIdDecl
         [`hγ₀ []]
         [(Term.typeSpec
           ":"
           («term_∈_»
            (Set.Data.Set.Image.«term_⁻¹'_» `extension " ⁻¹' " («term{_}» "{" [`γ₀] "}"))
            "∈"
            (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])))]
         ":="
         (Term.app
          `continuous_extension.continuous_at.preimage_mem_nhds
          [(Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `continuous_extension.continuous_at.preimage_mem_nhds
       [(Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero [`h])
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `continuous_extension.continuous_at.preimage_mem_nhds
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_»
       (Set.Data.Set.Image.«term_⁻¹'_» `extension " ⁻¹' " («term{_}» "{" [`γ₀] "}"))
       "∈"
       (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (TopologicalSpace.Topology.Basic.nhds "𝓝")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Set.Data.Set.Image.«term_⁻¹'_» `extension " ⁻¹' " («term{_}» "{" [`γ₀] "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term{_}» "{" [`γ₀] "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `extension
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 80, (some 81, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.intro "intro" [`h])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.arrow
         («term_≠_» `γ₀ "≠" (num "0"))
         "→"
         («term_↔_»
          («term_∈_»
           `x
           "∈"
           (Term.app
            `closure
            [(Set.Data.Set.Image.term_''_
              `coe
              " '' "
              (Set.«term{_|_}»
               "{"
               (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
               "|"
               («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
               "}"))]))
          "↔"
          («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))))
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.cases
             "cases"
             [(Tactic.casesTarget [] (Term.app `eq_or_ne [`γ₀ (num "0")]))]
             []
             [])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.simp
               "simp"
               []
               []
               ["only"]
               ["["
                [(Tactic.simpLemma [] [] `h)
                 ","
                 (Tactic.simpLemma
                  []
                  []
                  (Term.app
                   (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp)
                   [`h]))
                 ","
                 (Tactic.simpLemma [] [] `mem_set_of_eq)
                 ","
                 (Tactic.simpLemma [] [] `Valuation.map_zero)
                 ","
                 (Tactic.simpLemma [] [] `Units.zero_lt)
                 ","
                 (Tactic.simpLemma [] [] `iff_true_iff)]
                "]"]
               [])
              []
              (Tactic.apply "apply" `subset_closure)
              []
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(num "0")
                 ","
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Std.Tactic.Simpa.simpa
                      "simpa"
                      []
                      []
                      (Std.Tactic.Simpa.simpaArgsRest
                       []
                       []
                       ["only"]
                       [(Tactic.simpArgs
                         "["
                         [(Tactic.simpLemma [] [] `mem_set_of_eq)
                          ","
                          (Tactic.simpLemma [] [] `Valuation.map_zero)
                          ","
                          (Tactic.simpLemma [] [] `Units.zero_lt)
                          ","
                          (Tactic.simpLemma [] [] `true_and_iff)]
                         "]")]
                       []))])))]
                "⟩"))])
            []
            (tactic__
             (cdotTk (patternIgnore (token.«· » "·")))
             [(Tactic.exact "exact" (Term.app `this [`h]))])])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.exact "exact" (Term.app `this [`h]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `this [`h]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `this [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `this
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic__
       (cdotTk (patternIgnore (token.«· » "·")))
       [(Tactic.simp
         "simp"
         []
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `h)
           ","
           (Tactic.simpLemma
            []
            []
            (Term.app (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp) [`h]))
           ","
           (Tactic.simpLemma [] [] `mem_set_of_eq)
           ","
           (Tactic.simpLemma [] [] `Valuation.map_zero)
           ","
           (Tactic.simpLemma [] [] `Units.zero_lt)
           ","
           (Tactic.simpLemma [] [] `iff_true_iff)]
          "]"]
         [])
        []
        (Tactic.apply "apply" `subset_closure)
        []
        (Tactic.exact
         "exact"
         (Term.anonymousCtor
          "⟨"
          [(num "0")
           ","
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Std.Tactic.Simpa.simpa
                "simpa"
                []
                []
                (Std.Tactic.Simpa.simpaArgsRest
                 []
                 []
                 ["only"]
                 [(Tactic.simpArgs
                   "["
                   [(Tactic.simpLemma [] [] `mem_set_of_eq)
                    ","
                    (Tactic.simpLemma [] [] `Valuation.map_zero)
                    ","
                    (Tactic.simpLemma [] [] `Units.zero_lt)
                    ","
                    (Tactic.simpLemma [] [] `true_and_iff)]
                   "]")]
                 []))])))]
          "⟩"))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [(num "0")
         ","
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Std.Tactic.Simpa.simpa
              "simpa"
              []
              []
              (Std.Tactic.Simpa.simpaArgsRest
               []
               []
               ["only"]
               [(Tactic.simpArgs
                 "["
                 [(Tactic.simpLemma [] [] `mem_set_of_eq)
                  ","
                  (Tactic.simpLemma [] [] `Valuation.map_zero)
                  ","
                  (Tactic.simpLemma [] [] `Units.zero_lt)
                  ","
                  (Tactic.simpLemma [] [] `true_and_iff)]
                 "]")]
               []))])))]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(num "0")
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Simpa.simpa
             "simpa"
             []
             []
             (Std.Tactic.Simpa.simpaArgsRest
              []
              []
              ["only"]
              [(Tactic.simpArgs
                "["
                [(Tactic.simpLemma [] [] `mem_set_of_eq)
                 ","
                 (Tactic.simpLemma [] [] `Valuation.map_zero)
                 ","
                 (Tactic.simpLemma [] [] `Units.zero_lt)
                 ","
                 (Tactic.simpLemma [] [] `true_and_iff)]
                "]")]
              []))])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Simpa.simpa
           "simpa"
           []
           []
           (Std.Tactic.Simpa.simpaArgsRest
            []
            []
            ["only"]
            [(Tactic.simpArgs
              "["
              [(Tactic.simpLemma [] [] `mem_set_of_eq)
               ","
               (Tactic.simpLemma [] [] `Valuation.map_zero)
               ","
               (Tactic.simpLemma [] [] `Units.zero_lt)
               ","
               (Tactic.simpLemma [] [] `true_and_iff)]
              "]")]
            []))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Simpa.simpa
       "simpa"
       []
       []
       (Std.Tactic.Simpa.simpaArgsRest
        []
        []
        ["only"]
        [(Tactic.simpArgs
          "["
          [(Tactic.simpLemma [] [] `mem_set_of_eq)
           ","
           (Tactic.simpLemma [] [] `Valuation.map_zero)
           ","
           (Tactic.simpLemma [] [] `Units.zero_lt)
           ","
           (Tactic.simpLemma [] [] `true_and_iff)]
          "]")]
        []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `true_and_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.zero_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Valuation.map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_set_of_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.apply "apply" `subset_closure)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `subset_closure
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `h)
         ","
         (Tactic.simpLemma
          []
          []
          (Term.app (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp) [`h]))
         ","
         (Tactic.simpLemma [] [] `mem_set_of_eq)
         ","
         (Tactic.simpLemma [] [] `Valuation.map_zero)
         ","
         (Tactic.simpLemma [] [] `Units.zero_lt)
         ","
         (Tactic.simpLemma [] [] `iff_true_iff)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `iff_true_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Units.zero_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Valuation.map_zero
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mem_set_of_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp) [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `Valuation.zero_iff [(Term.hole "_")]) "." `mp)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Valuation.zero_iff [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Valuation.zero_iff
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Valuation.zero_iff [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.cases "cases" [(Tactic.casesTarget [] (Term.app `eq_or_ne [`γ₀ (num "0")]))] [] [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `eq_or_ne [`γ₀ (num "0")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'num', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `eq_or_ne
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.arrow
       («term_≠_» `γ₀ "≠" (num "0"))
       "→"
       («term_↔_»
        («term_∈_»
         `x
         "∈"
         (Term.app
          `closure
          [(Set.Data.Set.Image.term_''_
            `coe
            " '' "
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
             "|"
             («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
             "}"))]))
        "↔"
        («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_↔_»
       («term_∈_»
        `x
        "∈"
        (Term.app
         `closure
         [(Set.Data.Set.Image.term_''_
           `coe
           " '' "
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
            "|"
            («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
            "}"))]))
       "↔"
       («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `γ ":" [`Γ₀] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 20, term))
      («term_∈_»
       `x
       "∈"
       (Term.app
        `closure
        [(Set.Data.Set.Image.term_''_
          `coe
          " '' "
          (Set.«term{_|_}»
           "{"
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
           "|"
           («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
           "}"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `closure
       [(Set.Data.Set.Image.term_''_
         `coe
         " '' "
         (Set.«term{_|_}»
          "{"
          (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
          "|"
          («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
          "}"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Image.term_''_', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.Data.Set.Image.term_''_
       `coe
       " '' "
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
        "|"
        («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
       "|"
       («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `γ ":" [`Γ₀] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `v [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `v
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
      `coe
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 80, (some 81, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Set.Data.Set.Image.term_''_
      `coe
      " '' "
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
       "|"
       («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
       "}"))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `closure
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 21 >? 50, (some 51, term) <=? (some 20, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 20, (some 21, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     («term_↔_»
      («term_∈_»
       `x
       "∈"
       (Term.app
        `closure
        [(Term.paren
          "("
          (Set.Data.Set.Image.term_''_
           `coe
           " '' "
           (Set.«term{_|_}»
            "{"
            (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
            "|"
            («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
            "}"))
          ")")]))
      "↔"
      («term_<_» `γ₀ "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")")))
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
      («term_≠_» `γ₀ "≠" (num "0"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (num "0")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `γ₀
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25,
     term) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticLet_
       "let"
       (Term.letDecl (Term.letIdDecl `γ₀ [] [] ":=" (Term.app `extension_valuation [`x]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `extension_valuation [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extension_valuation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `x))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      («term_=_»
       (Term.app
        `closure
        [(Set.Data.Set.Image.term_''_
          `coe
          " '' "
          (Set.«term{_|_}»
           "{"
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [(group ":" `K)])
           "|"
           («term_<_» (Term.app `v [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
           "}"))])
       "="
       (Set.«term{_|_}»
        "{"
        (Std.ExtendedBinder.extBinder
         (Lean.binderIdent `x)
         [(group ":" (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))])
        "|"
        («term_<_»
         (Term.app `extensionValuation [`x])
         "<"
         (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder
        (Lean.binderIdent `x)
        [(group ":" (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]))])
       "|"
       («term_<_»
        (Term.app `extensionValuation [`x])
        "<"
        (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `extensionValuation [`x]) "<" (Term.typeAscription "(" `γ ":" [`Γ₀] ")"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription "(" `γ ":" [`Γ₀] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `extensionValuation [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extensionValuation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'-/-- failed to format: unknown constant 'group'
theorem
  closure_coe_completion_v_lt
  { γ : Γ₀ ˣ }
    :
      closure coe '' { x : K | v x < ( γ : Γ₀ ) }
        =
        { x : hat K | extensionValuation x < ( γ : Γ₀ ) }
  :=
    by
      ext x
        let γ₀ := extension_valuation x
        suffices
          γ₀ ≠ 0 → x ∈ closure coe '' { x : K | v x < ( γ : Γ₀ ) } ↔ γ₀ < ( γ : Γ₀ )
            by
              cases eq_or_ne γ₀ 0
                ·
                  simp
                      only
                      [
                        h
                          ,
                          Valuation.zero_iff _ . mp h
                          ,
                          mem_set_of_eq
                          ,
                          Valuation.map_zero
                          ,
                          Units.zero_lt
                          ,
                          iff_true_iff
                        ]
                    apply subset_closure
                    exact
                      ⟨
                        0
                          ,
                          by
                            simpa
                              only
                                [
                                  mem_set_of_eq , Valuation.map_zero , Units.zero_lt , true_and_iff
                                  ]
                        ⟩
                · exact this h
        intro h
        have
          hγ₀
            : extension ⁻¹' { γ₀ } ∈ 𝓝 x
            :=
            continuous_extension.continuous_at.preimage_mem_nhds
              LinearOrderedCommGroupWithZero.singleton_mem_nhds_of_ne_zero h
        rw [ mem_closure_iff_nhds' ]
        refine' ⟨ fun hx => _ , fun hx s hs => _ ⟩
        ·
          obtain ⟨ ⟨ - , y , hy₁ : v y < ( γ : Γ₀ ) , rfl ⟩ , hy₂ ⟩ := hx _ hγ₀
            replace hy₂ : v y = γ₀
            · simpa using hy₂
            rwa [ ← hy₂ ]
        ·
          obtain ⟨ y , hy₁ , hy₂ : ↑ y ∈ s ⟩ := completion.dense_range_coe.mem_nhds inter_mem hγ₀ hs
            replace hy₁ : v y = γ₀
            · simpa using hy₁
            rw [ ← hy₁ ] at hx
            exact ⟨ ⟨ y , ⟨ y , hx , rfl ⟩ ⟩ , hy₂ ⟩
#align valued.closure_coe_completion_v_lt Valued.closure_coe_completion_v_lt

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [] [(Command.noncomputable "noncomputable")] [] [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      [(Command.declId `valuedCompletion [])]
      (Command.declSig
       []
       (Term.typeSpec
        ":"
        (Term.app
         `Valued
         [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K]) `Γ₀])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField (Term.letDecl (Term.letIdDecl `V [] [] ":=" `extensionValuation)))
        []
        (Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `is_topological_valuation
           [`s]
           []
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.tacticSuffices_
                "suffices"
                (Term.sufficesDecl
                 []
                 (Term.app
                  `has_basis
                  [(Term.app
                    (TopologicalSpace.Topology.Basic.nhds "𝓝")
                    [(Term.typeAscription
                      "("
                      (num "0")
                      ":"
                      [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                      ")")])
                   (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`γ]
                     [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ"))]
                     "=>"
                     (Set.«term{_|_}»
                      "{"
                      (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
                      "|"
                      («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
                      "}")))])
                 (Term.byTactic'
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.mem_iff)] "]")
                      [])
                     []
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `exists_congr
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`γ]
                          []
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.simp "simp" [] [] [] [] [])])))))]))])))))
               []
               (Mathlib.Tactic.tacticSimp_rw__
                "simp_rw"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `closure_coe_completion_v_lt)]
                 "]")
                [])
               []
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj
                  (Term.app `has_basis_nhds_zero [`K `Γ₀])
                  "."
                  `has_basis_of_dense_inducing)
                 [`completion.dense_inducing_coe]))]))))))]
       [])
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.whereStructInst', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.tacticSuffices_
           "suffices"
           (Term.sufficesDecl
            []
            (Term.app
             `has_basis
             [(Term.app
               (TopologicalSpace.Topology.Basic.nhds "𝓝")
               [(Term.typeAscription
                 "("
                 (num "0")
                 ":"
                 [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
                 ")")])
              (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
              (Term.fun
               "fun"
               (Term.basicFun
                [`γ]
                [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ"))]
                "=>"
                (Set.«term{_|_}»
                 "{"
                 (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
                 "|"
                 («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
                 "}")))])
            (Term.byTactic'
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.mem_iff)] "]")
                 [])
                []
                (Tactic.exact
                 "exact"
                 (Term.app
                  `exists_congr
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`γ]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp "simp" [] [] [] [] [])])))))]))])))))
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `closure_coe_completion_v_lt)]
            "]")
           [])
          []
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `has_basis_nhds_zero [`K `Γ₀]) "." `has_basis_of_dense_inducing)
            [`completion.dense_inducing_coe]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        (Term.proj (Term.app `has_basis_nhds_zero [`K `Γ₀]) "." `has_basis_of_dense_inducing)
        [`completion.dense_inducing_coe]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `has_basis_nhds_zero [`K `Γ₀]) "." `has_basis_of_dense_inducing)
       [`completion.dense_inducing_coe])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `completion.dense_inducing_coe
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `has_basis_nhds_zero [`K `Γ₀]) "." `has_basis_of_dense_inducing)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `has_basis_nhds_zero [`K `Γ₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `has_basis_nhds_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `has_basis_nhds_zero [`K `Γ₀])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [(patternIgnore (token.«← » "←"))] `closure_coe_completion_v_lt)]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `closure_coe_completion_v_lt
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticSuffices_
       "suffices"
       (Term.sufficesDecl
        []
        (Term.app
         `has_basis
         [(Term.app
           (TopologicalSpace.Topology.Basic.nhds "𝓝")
           [(Term.typeAscription
             "("
             (num "0")
             ":"
             [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
             ")")])
          (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
          (Term.fun
           "fun"
           (Term.basicFun
            [`γ]
            [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ"))]
            "=>"
            (Set.«term{_|_}»
             "{"
             (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
             "|"
             («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
             "}")))])
        (Term.byTactic'
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.mem_iff)] "]") [])
            []
            (Tactic.exact
             "exact"
             (Term.app
              `exists_congr
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`γ]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic'', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `exists_congr
        [(Term.fun
          "fun"
          (Term.basicFun
           [`γ]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `exists_congr
       [(Term.fun
         "fun"
         (Term.basicFun
          [`γ]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`γ]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(Tactic.simp "simp" [] [] [] [] [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `exists_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `this.mem_iff)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `this.mem_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      (Term.app
       `has_basis
       [(Term.app
         (TopologicalSpace.Topology.Basic.nhds "𝓝")
         [(Term.typeAscription
           "("
           (num "0")
           ":"
           [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
           ")")])
        (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
        (Term.fun
         "fun"
         (Term.basicFun
          [`γ]
          [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ"))]
          "=>"
          (Set.«term{_|_}»
           "{"
           (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
           "|"
           («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
           "}")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`γ]
        [(Term.typeSpec ":" (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ"))]
        "=>"
        (Set.«term{_|_}»
         "{"
         (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
         "|"
         («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Set.«term{_|_}»
       "{"
       (Std.ExtendedBinder.extBinder (Lean.binderIdent `x) [])
       "|"
       («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
       "}")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<_» (Term.app `extension_valuation [`x]) "<" `γ)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `extension_valuation [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `extension_valuation
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Algebra.Group.Units.«term_ˣ» `Γ₀ "ˣ")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Γ₀
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
      `γ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `True
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.fun "fun" (Term.basicFun [(Term.hole "_")] [] "=>" `True))
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (TopologicalSpace.Topology.Basic.nhds "𝓝")
       [(Term.typeAscription
         "("
         (num "0")
         ":"
         [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
         ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.typeAscription
       "("
       (num "0")
       ":"
       [(Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])]
       ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app (Valued.Topology.Algebra.ValuedField.termhat "hat") [`K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Valued.Topology.Algebra.ValuedField.termhat "hat")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Valued.Topology.Algebra.ValuedField.termhat', expected 'Valued.Topology.Algebra.ValuedField.termhat._@.Topology.Algebra.ValuedField._hyg.18'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
noncomputable
  instance
    valuedCompletion
    : Valued hat K Γ₀
    where
      V := extensionValuation
        is_topological_valuation
          s
          :=
          by
            suffices
                has_basis
                    𝓝 ( 0 : hat K ) fun _ => True fun γ : Γ₀ ˣ => { x | extension_valuation x < γ }
                  by rw [ this.mem_iff ] exact exists_congr fun γ => by simp
              simp_rw [ ← closure_coe_completion_v_lt ]
              exact
                has_basis_nhds_zero K Γ₀ . has_basis_of_dense_inducing completion.dense_inducing_coe
#align valued.valued_completion Valued.valuedCompletion

end Valued

