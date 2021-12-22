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

variable {α : Type _} [MeasurableSpace α] {μ ν : Measureₓ α}

private theorem aux {m : ℕ} {γ d : ℝ} (h : γ - (1 / 2) ^ m < d) : ((γ - 2*(1 / 2) ^ m)+(1 / 2) ^ m) ≤ d := by
  linarith

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " **Hahn decomposition theorem** -/")] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `hahn_decomposition [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `is_finite_measure [`μ]) "]")
    (Term.instBinder "[" [] (Term.app `is_finite_measure [`ν]) "]")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] []))
     ","
     («term_∧_»
      (Term.app `MeasurableSet [`s])
      "∧"
      («term_∧_»
       (Term.forall
        "∀"
        [(Term.simpleBinder [`t] [])]
        ","
        (Term.arrow
         (Term.app `MeasurableSet [`t])
         "→"
         (Term.arrow (Init.Core.«term_⊆_» `t " ⊆ " `s) "→" («term_≤_» (Term.app `ν [`t]) "≤" (Term.app `μ [`t])))))
       "∧"
       (Term.forall
        "∀"
        [(Term.simpleBinder [`t] [])]
        ","
        (Term.arrow
         (Term.app `MeasurableSet [`t])
         "→"
         (Term.arrow
          (Init.Core.«term_⊆_» `t " ⊆ " (Order.BooleanAlgebra.«term_ᶜ» `s "ᶜ"))
          "→"
          («term_≤_» (Term.app `μ [`t]) "≤" (Term.app `ν [`t]))))))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `d
           [(Term.typeSpec ":" (Term.arrow (Term.app `Set [`α]) "→" (Data.Real.Basic.termℝ "ℝ")))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             («term_-_»
              (Term.paren
               "("
               [(Term.proj (Term.app `μ [`s]) "." `toNnreal) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
               ")")
              "-"
              (Term.proj (Term.app `ν [`s]) "." `toNnreal)))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `c
           [(Term.typeSpec ":" (Term.app `Set [(Data.Real.Basic.termℝ "ℝ")]))]
           ":="
           (Set.Data.Set.Basic.term_''_ `d " '' " (Set.«term{_|_}» "{" `s "|" (Term.app `MeasurableSet [`s]) "}")))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl (Term.letIdDecl `γ [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))] ":=" (Term.app `Sup [`c]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hμ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [])]
              ","
              («term_≠_» (Term.app `μ [`s]) "≠" (Data.Real.Ennreal.«term∞» "∞"))))]
           ":="
           (Term.app `measure_ne_top [`μ]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hν []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [])]
              ","
              («term_≠_» (Term.app `ν [`s]) "≠" (Data.Real.Ennreal.«term∞» "∞"))))]
           ":="
           (Term.app `measure_ne_top [`ν]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`to_nnreal_μ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [])]
              ","
              («term_=_»
               (Term.paren
                "("
                [(Term.proj (Term.app `μ [`s]) "." `toNnreal)
                 [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                ")")
               "="
               (Term.app `μ [`s]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             («term_$__» `Ennreal.coe_to_nnreal "$" (Term.app `hμ [(Term.hole "_")])))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`to_nnreal_ν []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [])]
              ","
              («term_=_»
               (Term.paren
                "("
                [(Term.proj (Term.app `ν [`s]) "." `toNnreal)
                 [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
                ")")
               "="
               (Term.app `ν [`s]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             («term_$__» `Ennreal.coe_to_nnreal "$" (Term.app `hν [(Term.hole "_")])))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`d_empty []]
           [(Term.typeSpec ":" («term_=_» (Term.app `d [(«term∅» "∅")]) "=" (numLit "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.change
                 "change"
                 («term_=_» («term_-_» (Term.hole "_") "-" (Term.hole "_")) "=" (Term.hole "_"))
                 [])
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `measure_empty)
                   ","
                   (Tactic.rwRule [] `measure_empty)
                   ","
                   (Tactic.rwRule [] `sub_self)]
                  "]")
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`d_split []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s `t] [])]
              ","
              (Term.arrow
               (Term.app `MeasurableSet [`s])
               "→"
               (Term.arrow
                (Term.app `MeasurableSet [`t])
                "→"
                («term_=_»
                 (Term.app `d [`s])
                 "="
                 (Init.Logic.«term_+_»
                  (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)])
                  "+"
                  (Term.app `d [(Init.Core.«term_∩_» `s " ∩ " `t)])))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`s `t `hs `ht]) [])
               (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `d)] "]"] []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule ["←"] (Term.app `measure_inter_add_diff [`s `ht]))
                   ","
                   (Tactic.rwRule ["←"] (Term.app `measure_inter_add_diff [`s `ht]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app
                     `Ennreal.to_nnreal_add
                     [(Term.app `hμ [(Term.hole "_")]) (Term.app `hμ [(Term.hole "_")])]))
                   ","
                   (Tactic.rwRule
                    []
                    (Term.app
                     `Ennreal.to_nnreal_add
                     [(Term.app `hν [(Term.hole "_")]) (Term.app `hν [(Term.hole "_")])]))
                   ","
                   (Tactic.rwRule [] `Nnreal.coe_add)
                   ","
                   (Tactic.rwRule [] `Nnreal.coe_add)]
                  "]")
                 [])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `sub_eq_add_neg) "," (Tactic.simpLemma [] [] `neg_add)] "]"]
                 [])
                [])
               (group (Tactic.acRfl "ac_rfl") [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`d_Union []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α])))])]
              ","
              (Term.arrow
               (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `s [`n])]))
               "→"
               (Term.arrow
                (Term.app `Monotone [`s])
                "→"
                (Term.app
                 `tendsto
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `s [`n])])))
                  `at_top
                  (Term.app
                   (Topology.Basic.term𝓝 "𝓝")
                   [(Term.app
                     `d
                     [(Set.Data.Set.Lattice.«term⋃_,_»
                       "⋃"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                       ", "
                       (Term.app `s [`n]))])])])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`s `hs `hm]) [])
               (group
                (Tactic.«tactic_<;>_»
                 (Tactic.refine' "refine'" (Term.app `tendsto.sub [(Term.hole "_") (Term.hole "_")]))
                 "<;>"
                 (Tactic.refine'
                  "refine'"
                  («term_$__»
                   (Term.proj `Nnreal.tendsto_coe "." (fieldIdx "2"))
                   "$"
                   («term_$__»
                    (Term.proj (Term.app `Ennreal.tendsto_to_nnreal [(Term.hole "_")]) "." `comp)
                    "$"
                    (Term.app `tendsto_measure_Union [`hs `hm])))))
                [])
               (group (Tactic.exact "exact" (Term.app `hμ [(Term.hole "_")])) [])
               (group (Tactic.exact "exact" (Term.app `hν [(Term.hole "_")])) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`d_Inter []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α])))])]
              ","
              (Term.arrow
               (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `s [`n])]))
               "→"
               (Term.arrow
                (Term.forall
                 "∀"
                 [(Term.simpleBinder [`n `m] [])]
                 ","
                 (Term.arrow
                  («term_≤_» `n "≤" `m)
                  "→"
                  (Init.Core.«term_⊆_» (Term.app `s [`m]) " ⊆ " (Term.app `s [`n]))))
                "→"
                (Term.app
                 `tendsto
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `s [`n])])))
                  `at_top
                  (Term.app
                   (Topology.Basic.term𝓝 "𝓝")
                   [(Term.app
                     `d
                     [(Set.Data.Set.Lattice.«term⋂_,_»
                       "⋂"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                       ", "
                       (Term.app `s [`n]))])])])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`s `hs `hm]) [])
               (group
                (Tactic.«tactic_<;>_»
                 (Tactic.refine' "refine'" (Term.app `tendsto.sub [(Term.hole "_") (Term.hole "_")]))
                 "<;>"
                 (Tactic.refine'
                  "refine'"
                  («term_$__»
                   (Term.proj `Nnreal.tendsto_coe "." (fieldIdx "2"))
                   "$"
                   («term_$__»
                    (Term.proj («term_$__» `Ennreal.tendsto_to_nnreal "$" (Term.hole "_")) "." `comp)
                    "$"
                    (Term.app `tendsto_measure_Inter [`hs `hm (Term.hole "_")])))))
                [])
               (group
                (exacts
                 "exacts"
                 "["
                 [(Term.app `hμ [(Term.hole "_")])
                  ","
                  (Term.anonymousCtor "⟨" [(numLit "0") "," (Term.app `hμ [(Term.hole "_")])] "⟩")
                  ","
                  (Term.app `hν [(Term.hole "_")])
                  ","
                  (Term.anonymousCtor "⟨" [(numLit "0") "," (Term.app `hν [(Term.hole "_")])] "⟩")]
                 "]")
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`bdd_c []]
           [(Term.typeSpec ":" (Term.app `BddAbove [`c]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.use "use" [(Term.proj (Term.app `μ [`univ]) "." `toNnreal)]) [])
               (group
                (Tactic.rintro
                 "rintro"
                 [(Tactic.rintroPat.one (Tactic.rcasesPat.one `r))
                  (Tactic.rintroPat.one
                   (Tactic.rcasesPat.tuple
                    "⟨"
                    [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                     ","
                     (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                    "⟩"))]
                 [])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `le_transₓ
                  [(«term_$__»
                    (Term.app `sub_le_self [(Term.hole "_")])
                    "$"
                    (Term.app `Nnreal.coe_nonneg [(Term.hole "_")]))
                   (Term.hole "_")]))
                [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Nnreal.coe_le_coe)
                   ","
                   (Tactic.rwRule ["←"] `Ennreal.coe_le_coe)
                   ","
                   (Tactic.rwRule [] `to_nnreal_μ)
                   ","
                   (Tactic.rwRule [] `to_nnreal_μ)]
                  "]")
                 [])
                [])
               (group
                (Tactic.exact "exact" (Term.app `measure_mono [(Term.app `subset_univ [(Term.hole "_")])]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`c_nonempty []]
           [(Term.typeSpec ":" `c.nonempty)]
           ":="
           (Term.app
            `nonempty.image
            [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," `MeasurableSet.empty] "⟩")]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`d_le_γ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [])]
              ","
              (Term.arrow (Term.app `MeasurableSet [`s]) "→" («term_≤_» (Term.app `d [`s]) "≤" `γ))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s `hs] [])]
             "=>"
             (Term.app `le_cSup [`bdd_c (Term.anonymousCtor "⟨" [`s "," `hs "," `rfl] "⟩")]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Set [`α])]))
               ","
               («term_∧_»
                (Term.app `MeasurableSet [`s])
                "∧"
                («term_<_»
                 («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
                 "<"
                 (Term.app `d [`s]))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n]) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec
                     ":"
                     («term_<_»
                      («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
                      "<"
                      `γ))]
                   ":="
                   (Term.app `sub_lt_self [`γ (Term.app `pow_pos [(Term.app `half_pos [`zero_lt_one]) `n])]))))
                [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget [] (Term.app `exists_lt_of_lt_cSup [`c_nonempty `this]))]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
                    ","
                    (Tactic.rcasesPatLo
                     (Tactic.rcasesPatMed
                      [(Tactic.rcasesPat.tuple
                        "⟨"
                        [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                         ","
                         (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                        "⟩")])
                     [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
                   "⟩")])
                [])
               (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`s "," `hs "," `hlt] "⟩")) [])]))))))
        [])
       (group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `Classical.axiom_of_choice [`this]))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `e)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `he)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.change
         "change"
         (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α]))
         [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`he₁ []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `e [`n])])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `he [`n]) "." (fieldIdx "1")))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`he₂ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              («term_<_»
               («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
               "<"
               (Term.app `d [(Term.app `e [`n])]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `he [`n]) "." (fieldIdx "2")))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `f
           [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`n `m] [])]
             "=>"
             (Term.app
              (Term.proj (Term.app `Finset.ico [`n (Init.Logic.«term_+_» `m "+" (numLit "1"))]) "." `inf)
              [`e]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hf []]
           [(Term.typeSpec
             ":"
             (Term.forall "∀" [(Term.simpleBinder [`n `m] [])] "," (Term.app `MeasurableSet [(Term.app `f [`n `m])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `m]) [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["[" [(Tactic.simpLemma [] [] `f) "," (Tactic.simpLemma [] [] `Finset.inf_eq_infi)] "]"]
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `MeasurableSet.bInter
                  [(Term.app `countable_encodable [(Term.hole "_")])
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i (Term.hole "_")] [])]
                     "=>"
                     (Term.app `he₁ [(Term.hole "_")])))]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`f_subset_f []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.implicitBinder "{" [`a `b `c `d] [] "}")]
              ","
              (Term.arrow
               («term_≤_» `a "≤" `b)
               "→"
               (Term.arrow
                («term_≤_» `c "≤" `d)
                "→"
                (Init.Core.«term_⊆_» (Term.app `f [`a `d]) " ⊆ " (Term.app `f [`b `c]))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`a `b `c `d `hab `hcd]) [])
               (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Finset.inf_eq_infi) "," (Tactic.rwRule [] `Finset.inf_eq_infi)]
                  "]")
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `bInter_subset_bInter_left
                  [(«term_$__» (Term.app `Finset.Ico_subset_Ico [`hab]) "$" (Term.app `Nat.succ_le_succₓ [`hcd]))]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`f_succ []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n `m] [])]
              ","
              (Term.arrow
               («term_≤_» `n "≤" `m)
               "→"
               («term_=_»
                (Term.app `f [`n (Init.Logic.«term_+_» `m "+" (numLit "1"))])
                "="
                (Init.Core.«term_∩_»
                 (Term.app `f [`n `m])
                 " ∩ "
                 (Term.app `e [(Init.Logic.«term_+_» `m "+" (numLit "1"))]))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `m `hnm]) [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   []
                   [(Term.typeSpec ":" («term_≤_» `n "≤" (Init.Logic.«term_+_» `m "+" (numLit "1"))))]
                   ":="
                   (Term.app `le_of_ltₓ [(Term.app `Nat.succ_le_succₓ [`hnm])]))))
                [])
               (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] []) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] (Term.app `Nat.Ico_succ_right_eq_insert_Ico [`this]))
                   ","
                   (Tactic.rwRule [] `Finset.inf_insert)
                   ","
                   (Tactic.rwRule [] `Set.inter_comm)]
                  "]")
                 [])
                [])
               (group (Tactic.tacticRfl "rfl") [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`le_d_f []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n `m] [])]
              ","
              (Term.arrow
               («term_≤_» `m "≤" `n)
               "→"
               («term_≤_»
                (Init.Logic.«term_+_»
                 («term_-_»
                  `γ
                  "-"
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                 "+"
                 («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
                "≤"
                (Term.app `d [(Term.app `f [`m `n])])))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`n `m `h]) [])
               (group
                (Tactic.refine' "refine'" (Term.app `Nat.le_induction [(Term.hole "_") (Term.hole "_") `n `h]))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `he₂ [`m]))))
                     [])
                    (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] []) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Nat.Ico_succ_singleton) "," (Tactic.rwRule [] `Finset.inf_singleton)]
                       "]")
                      [])
                     [])
                    (group (Tactic.exact "exact" (Term.app `aux [`this])) [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.intro
                      "intro"
                      [`n (Term.paren "(" [`hmn [(Term.typeAscription ":" («term_≤_» `m "≤" `n))]] ")") `ih])
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        []
                        [(Term.typeSpec
                          ":"
                          («term_≤_»
                           (Init.Logic.«term_+_»
                            `γ
                            "+"
                            (Init.Logic.«term_+_»
                             («term_-_»
                              `γ
                              "-"
                              (Finset.Data.Finset.Fold.«term_*_»
                               (numLit "2")
                               "*"
                               («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                             "+"
                             («term_^_»
                              («term_/_» (numLit "1") "/" (numLit "2"))
                              "^"
                              (Init.Logic.«term_+_» `n "+" (numLit "1")))))
                           "≤"
                           (Init.Logic.«term_+_»
                            `γ
                            "+"
                            (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])]))))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (tacticCalc_
                              "calc"
                              [(calcStep
                                («term_≤_»
                                 (Init.Logic.«term_+_»
                                  `γ
                                  "+"
                                  (Init.Logic.«term_+_»
                                   («term_-_»
                                    `γ
                                    "-"
                                    (Finset.Data.Finset.Fold.«term_*_»
                                     (numLit "2")
                                     "*"
                                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                   "+"
                                   («term_^_»
                                    («term_/_» (numLit "1") "/" (numLit "2"))
                                    "^"
                                    (Init.Logic.«term_+_» `n "+" (numLit "1")))))
                                 "≤"
                                 (Init.Logic.«term_+_»
                                  `γ
                                  "+"
                                  (Init.Logic.«term_+_»
                                   («term_-_»
                                    `γ
                                    "-"
                                    (Finset.Data.Finset.Fold.«term_*_»
                                     (numLit "2")
                                     "*"
                                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                   "+"
                                   («term_-_»
                                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)
                                    "-"
                                    («term_^_»
                                     («term_/_» (numLit "1") "/" (numLit "2"))
                                     "^"
                                     (Init.Logic.«term_+_» `n "+" (numLit "1")))))))
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.refine'
                                      "refine'"
                                      (Term.app
                                       `add_le_add_left
                                       [(Term.app `add_le_add_left [(Term.hole "_") (Term.hole "_")]) `γ]))
                                     [])
                                    (group
                                     (Tactic.simp
                                      "simp"
                                      []
                                      ["only"]
                                      ["["
                                       [(Tactic.simpLemma [] [] `pow_addₓ)
                                        ","
                                        (Tactic.simpLemma [] [] `pow_oneₓ)
                                        ","
                                        (Tactic.simpLemma [] [] `le_sub_iff_add_le)]
                                       "]"]
                                      [])
                                     [])
                                    (group (Tactic.linarith "linarith" [] [] []) [])]))))
                               (calcStep
                                («term_=_»
                                 (Term.hole "_")
                                 "="
                                 (Init.Logic.«term_+_»
                                  («term_-_»
                                   `γ
                                   "-"
                                   («term_^_»
                                    («term_/_» (numLit "1") "/" (numLit "2"))
                                    "^"
                                    (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                                  "+"
                                  (Init.Logic.«term_+_»
                                   («term_-_»
                                    `γ
                                    "-"
                                    (Finset.Data.Finset.Fold.«term_*_»
                                     (numLit "2")
                                     "*"
                                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                   "+"
                                   («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))))
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.«tactic_<;>_»
                                      (Tactic.simp
                                       "simp"
                                       []
                                       ["only"]
                                       ["[" [(Tactic.simpLemma [] [] `sub_eq_add_neg)] "]"]
                                       [])
                                      "<;>"
                                      (Tactic.acRfl "ac_rfl"))
                                     [])]))))
                               (calcStep
                                («term_≤_»
                                 (Term.hole "_")
                                 "≤"
                                 (Init.Logic.«term_+_»
                                  (Term.app `d [(Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
                                  "+"
                                  (Term.app `d [(Term.app `f [`m `n])])))
                                ":="
                                (Term.app
                                 `add_le_add
                                 [(«term_$__» `le_of_ltₓ "$" (Term.app `he₂ [(Term.hole "_")])) `ih]))
                               (calcStep
                                («term_≤_»
                                 (Term.hole "_")
                                 "≤"
                                 (Init.Logic.«term_+_»
                                  (Init.Logic.«term_+_»
                                   (Term.app `d [(Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
                                   "+"
                                   (Term.app
                                    `d
                                    [(Init.Core.«term_\_»
                                      (Term.app `f [`m `n])
                                      " \\ "
                                      (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))]))
                                  "+"
                                  (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.rwSeq
                                      "rw"
                                      []
                                      (Tactic.rwRuleSeq
                                       "["
                                       [(Tactic.rwRule [] (Term.app `f_succ [(Term.hole "_") (Term.hole "_") `hmn]))
                                        ","
                                        (Tactic.rwRule
                                         []
                                         (Term.app
                                          `d_split
                                          [(Term.app `f [`m `n])
                                           (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                           (Term.app `hf [(Term.hole "_") (Term.hole "_")])
                                           (Term.app `he₁ [(Term.hole "_")])]))
                                        ","
                                        (Tactic.rwRule [] `add_assocₓ)]
                                       "]")
                                      [])
                                     [])]))))
                               (calcStep
                                («term_=_»
                                 (Term.hole "_")
                                 "="
                                 (Init.Logic.«term_+_»
                                  (Term.app
                                   `d
                                   [(Init.Core.«term_∪_»
                                     (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                     " ∪ "
                                     (Term.app `f [`m `n]))])
                                  "+"
                                  (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                                ":="
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(group
                                     (Tactic.rwSeq
                                      "rw"
                                      []
                                      (Tactic.rwRuleSeq
                                       "["
                                       [(Tactic.rwRule
                                         []
                                         (Term.app
                                          `d_split
                                          [(Init.Core.«term_∪_»
                                            (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                            " ∪ "
                                            (Term.app `f [`m `n]))
                                           (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                                        ","
                                        (Tactic.rwRule [] `union_diff_left)
                                        ","
                                        (Tactic.rwRule [] `union_inter_cancel_left)]
                                       "]")
                                      [])
                                     [])
                                    (group (Tactic.acRfl "ac_rfl") [])
                                    (group
                                     (Tactic.exact
                                      "exact"
                                      (Term.app
                                       (Term.proj (Term.app `he₁ [(Term.hole "_")]) "." `union)
                                       [(Term.app `hf [(Term.hole "_") (Term.hole "_")])]))
                                     [])
                                    (group (Tactic.exact "exact" (Term.app `he₁ [(Term.hole "_")])) [])]))))
                               (calcStep
                                («term_≤_»
                                 (Term.hole "_")
                                 "≤"
                                 (Init.Logic.«term_+_»
                                  `γ
                                  "+"
                                  (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                                ":="
                                (Term.app
                                 `add_le_add_right
                                 [(«term_$__»
                                   (Term.app `d_le_γ [(Term.hole "_")])
                                   "$"
                                   (Term.app
                                    (Term.proj (Term.app `he₁ [(Term.hole "_")]) "." `union)
                                    [(Term.app `hf [(Term.hole "_") (Term.hole "_")])]))
                                  (Term.hole "_")]))])
                             [])]))))))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1")) [`this]))
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `s
           []
           ":="
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
            ", "
            (Set.Data.Set.Lattice.«term⋂_,_»
             "⋂"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
             ", "
             (Term.app `f [`m `n]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`γ_le_d_s []]
           [(Term.typeSpec ":" («term_≤_» `γ "≤" (Term.app `d [`s])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hγ []]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `tendsto
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                         "=>"
                         («term_-_»
                          `γ
                          "-"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (numLit "2")
                           "*"
                           («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                       `at_top
                       (Term.app (Topology.Basic.term𝓝 "𝓝") [`γ])]))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.tacticSuffices_
                         "suffices"
                         (Term.sufficesDecl
                          []
                          (Term.app
                           `tendsto
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                              "=>"
                              («term_-_»
                               `γ
                               "-"
                               (Finset.Data.Finset.Fold.«term_*_»
                                (numLit "2")
                                "*"
                                («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                            `at_top
                            (Term.app
                             (Topology.Basic.term𝓝 "𝓝")
                             [(«term_-_» `γ "-" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (numLit "0")))])])
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))
                        [])
                       (group
                        (Tactic.exact
                         "exact"
                         («term_$__»
                          `tendsto_const_nhds.sub
                          "$"
                          («term_$__»
                           `tendsto_const_nhds.mul
                           "$"
                           (Term.app
                            `tendsto_pow_at_top_nhds_0_of_lt_1
                            [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one))
                             (Term.app `half_lt_self [`zero_lt_one])]))))
                        [])]))))))
                [])
               (group
                (Tactic.tacticHave_
                 "have"
                 (Term.haveDecl
                  (Term.haveIdDecl
                   [`hd []]
                   [(Term.typeSpec
                     ":"
                     (Term.app
                      `tendsto
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`m] [])]
                         "=>"
                         (Term.app
                          `d
                          [(Set.Data.Set.Lattice.«term⋂_,_»
                            "⋂"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                            ", "
                            (Term.app `f [`m `n]))])))
                       `at_top
                       (Term.app
                        (Topology.Basic.term𝓝 "𝓝")
                        [(Term.app
                          `d
                          [(Set.Data.Set.Lattice.«term⋃_,_»
                            "⋃"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
                            ", "
                            (Set.Data.Set.Lattice.«term⋂_,_»
                             "⋂"
                             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                             ", "
                             (Term.app `f [`m `n])))])])]))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.refine' "refine'" (Term.app `d_Union [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.intro "intro" [`n]) [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `MeasurableSet.Inter
                               [(Term.fun
                                 "fun"
                                 (Term.basicFun
                                  [(Term.simpleBinder [`m] [])]
                                  "=>"
                                  (Term.app `hf [(Term.hole "_") (Term.hole "_")])))]))
                             [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.exact
                              "exact"
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [(Term.simpleBinder [`n `m `hnm] [])]
                                "=>"
                                (Term.app
                                 `subset_Inter
                                 [(Term.fun
                                   "fun"
                                   (Term.basicFun
                                    [(Term.simpleBinder [`i] [])]
                                    "=>"
                                    («term_$__»
                                     (Term.app `subset.trans [(Term.app `Inter_subset [(Term.app `f [`n]) `i])])
                                     "$"
                                     («term_$__»
                                      (Term.app `f_subset_f [`hnm])
                                      "$"
                                      (Term.app `le_reflₓ [(Term.hole "_")])))))]))))
                             [])])))
                        [])]))))))
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `le_of_tendsto_of_tendsto'
                  [`hγ `hd (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.hole "_")))]))
                [])
               (group
                (Tactic.tacticHave_
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
                        (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
                       `at_top
                       (Term.app
                        (Topology.Basic.term𝓝 "𝓝")
                        [(Term.app
                          `d
                          [(Set.Data.Set.Lattice.«term⋂_,_»
                            "⋂"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                            ", "
                            (Term.app `f [`m `n]))])])]))]
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.intro "intro" [`n]) [])
                            (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
                        [])
                       (group
                        (Tactic.«tactic·._»
                         "·"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group (Tactic.intro "intro" [`n `m `hnm]) [])
                            (group
                             (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm]))
                             [])])))
                        [])]))))))
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `ge_of_tendsto
                  [`this
                   (Term.app
                    (Term.proj `eventually_at_top "." (fieldIdx "2"))
                    [(Term.anonymousCtor
                      "⟨"
                      [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
                      "⟩")])]))
                [])
               (group
                (Tactic.change
                 "change"
                 («term_≤_»
                  («term_-_»
                   `γ
                   "-"
                   (Finset.Data.Finset.Fold.«term_*_»
                    (numLit "2")
                    "*"
                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                  "≤"
                  (Term.app `d [(Term.app `f [`m `n])]))
                 [])
                [])
               (group
                (Tactic.refine'
                 "refine'"
                 (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])]))
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `le_add_of_le_of_nonneg
                  [(Term.app `le_reflₓ [(Term.hole "_")])
                   (Term.app
                    `pow_nonneg
                    [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hs []]
           [(Term.typeSpec ":" (Term.app `MeasurableSet [`s]))]
           ":="
           (Term.app
            `MeasurableSet.Union
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n] [])]
               "=>"
               (Term.app
                `MeasurableSet.Inter
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`m] [])]
                   "=>"
                   (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])))]))))
        [])
       (group
        (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_") "," (Term.hole "_")] "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`t `ht `hts]) [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `d [`t])))]
                ":="
                («term_$__»
                 (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
                 "$"
                 (calc
                  "calc"
                  [(calcStep
                    («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.«tactic_<;>_»
                          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                          "<;>"
                          (Tactic.exact "exact" `γ_le_d_s))
                         [])]))))
                   (calcStep
                    («term_=_»
                     (Term.hole "_")
                     "="
                     (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq
                           "["
                           [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
                            ","
                            (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
                           "]")
                          [])
                         [])]))))
                   (calcStep
                    («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
                    ":="
                    (Term.app
                     `add_le_add
                     [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])])
                      (Term.app `le_reflₓ [(Term.hole "_")])]))])))))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `to_nnreal_μ)
                ","
                (Tactic.rwRule ["←"] `to_nnreal_ν)
                ","
                (Tactic.rwRule [] `Ennreal.coe_le_coe)
                ","
                (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
               "]")
              [])
             [])
            (group
             (Tactic.simpa
              "simpa"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `d)
                ","
                (Tactic.simpLemma [] [] `le_sub_iff_add_le)
                ","
                (Tactic.simpLemma [] [] `zero_addₓ)]
               "]"]
              []
              ["using" `this])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`t `ht `hts]) [])
            (group (Tactic.have'' "have" [] [(Term.typeSpec ":" («term_≤_» (Term.app `d [`t]) "≤" (numLit "0")))]) [])
            (group
             (Tactic.exact
              "exact"
              («term_$__»
               (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
               "$"
               (calc
                "calc"
                [(calcStep
                  («term_≤_»
                   (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
                   "≤"
                   (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
                  ":="
                  (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq
                         "["
                         [(Tactic.rwRule
                           []
                           (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
                          ","
                          (Tactic.rwRule [] `union_diff_right)
                          ","
                          (Tactic.rwRule [] `union_inter_cancel_right)
                          ","
                          (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
                         "]")
                        [])
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
                          "=>"
                          (Term.app `hts [`hat `has]))))
                       [])]))))
                 (calcStep
                  («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.«tactic_<;>_»
                        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                        "<;>"
                        (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
                       [])]))))])))
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule ["←"] `to_nnreal_μ)
                ","
                (Tactic.rwRule ["←"] `to_nnreal_ν)
                ","
                (Tactic.rwRule [] `Ennreal.coe_le_coe)
                ","
                (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
               "]")
              [])
             [])
            (group
             (Tactic.simpa
              "simpa"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `d)
                ","
                (Tactic.simpLemma [] [] `sub_le_iff_le_add)
                ","
                (Tactic.simpLemma [] [] `zero_addₓ)]
               "]"]
              []
              ["using" `this])
             [])])))
        [])])))
   [])
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.def'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `d
          [(Term.typeSpec ":" (Term.arrow (Term.app `Set [`α]) "→" (Data.Real.Basic.termℝ "ℝ")))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            («term_-_»
             (Term.paren
              "("
              [(Term.proj (Term.app `μ [`s]) "." `toNnreal) [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]]
              ")")
             "-"
             (Term.proj (Term.app `ν [`s]) "." `toNnreal)))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `c
          [(Term.typeSpec ":" (Term.app `Set [(Data.Real.Basic.termℝ "ℝ")]))]
          ":="
          (Set.Data.Set.Basic.term_''_ `d " '' " (Set.«term{_|_}» "{" `s "|" (Term.app `MeasurableSet [`s]) "}")))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl (Term.letIdDecl `γ [(Term.typeSpec ":" (Data.Real.Basic.termℝ "ℝ"))] ":=" (Term.app `Sup [`c]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hμ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [])]
             ","
             («term_≠_» (Term.app `μ [`s]) "≠" (Data.Real.Ennreal.«term∞» "∞"))))]
          ":="
          (Term.app `measure_ne_top [`μ]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hν []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [])]
             ","
             («term_≠_» (Term.app `ν [`s]) "≠" (Data.Real.Ennreal.«term∞» "∞"))))]
          ":="
          (Term.app `measure_ne_top [`ν]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`to_nnreal_μ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [])]
             ","
             («term_=_»
              (Term.paren
               "("
               [(Term.proj (Term.app `μ [`s]) "." `toNnreal)
                [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
               ")")
              "="
              (Term.app `μ [`s]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            («term_$__» `Ennreal.coe_to_nnreal "$" (Term.app `hμ [(Term.hole "_")])))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`to_nnreal_ν []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [])]
             ","
             («term_=_»
              (Term.paren
               "("
               [(Term.proj (Term.app `ν [`s]) "." `toNnreal)
                [(Term.typeAscription ":" (Data.Real.Ennreal.«termℝ≥0∞» "ℝ≥0∞"))]]
               ")")
              "="
              (Term.app `ν [`s]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            («term_$__» `Ennreal.coe_to_nnreal "$" (Term.app `hν [(Term.hole "_")])))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d_empty []]
          [(Term.typeSpec ":" («term_=_» (Term.app `d [(«term∅» "∅")]) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.change
                "change"
                («term_=_» («term_-_» (Term.hole "_") "-" (Term.hole "_")) "=" (Term.hole "_"))
                [])
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `measure_empty)
                  ","
                  (Tactic.rwRule [] `measure_empty)
                  ","
                  (Tactic.rwRule [] `sub_self)]
                 "]")
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d_split []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s `t] [])]
             ","
             (Term.arrow
              (Term.app `MeasurableSet [`s])
              "→"
              (Term.arrow
               (Term.app `MeasurableSet [`t])
               "→"
               («term_=_»
                (Term.app `d [`s])
                "="
                (Init.Logic.«term_+_»
                 (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)])
                 "+"
                 (Term.app `d [(Init.Core.«term_∩_» `s " ∩ " `t)])))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `t `hs `ht]) [])
              (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `d)] "]"] []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule ["←"] (Term.app `measure_inter_add_diff [`s `ht]))
                  ","
                  (Tactic.rwRule ["←"] (Term.app `measure_inter_add_diff [`s `ht]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `Ennreal.to_nnreal_add
                    [(Term.app `hμ [(Term.hole "_")]) (Term.app `hμ [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule
                   []
                   (Term.app
                    `Ennreal.to_nnreal_add
                    [(Term.app `hν [(Term.hole "_")]) (Term.app `hν [(Term.hole "_")])]))
                  ","
                  (Tactic.rwRule [] `Nnreal.coe_add)
                  ","
                  (Tactic.rwRule [] `Nnreal.coe_add)]
                 "]")
                [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `sub_eq_add_neg) "," (Tactic.simpLemma [] [] `neg_add)] "]"]
                [])
               [])
              (group (Tactic.acRfl "ac_rfl") [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d_Union []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α])))])]
             ","
             (Term.arrow
              (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `s [`n])]))
              "→"
              (Term.arrow
               (Term.app `Monotone [`s])
               "→"
               (Term.app
                `tendsto
                [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `s [`n])])))
                 `at_top
                 (Term.app
                  (Topology.Basic.term𝓝 "𝓝")
                  [(Term.app
                    `d
                    [(Set.Data.Set.Lattice.«term⋃_,_»
                      "⋃"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                      ", "
                      (Term.app `s [`n]))])])])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `hs `hm]) [])
              (group
               (Tactic.«tactic_<;>_»
                (Tactic.refine' "refine'" (Term.app `tendsto.sub [(Term.hole "_") (Term.hole "_")]))
                "<;>"
                (Tactic.refine'
                 "refine'"
                 («term_$__»
                  (Term.proj `Nnreal.tendsto_coe "." (fieldIdx "2"))
                  "$"
                  («term_$__»
                   (Term.proj (Term.app `Ennreal.tendsto_to_nnreal [(Term.hole "_")]) "." `comp)
                   "$"
                   (Term.app `tendsto_measure_Union [`hs `hm])))))
               [])
              (group (Tactic.exact "exact" (Term.app `hμ [(Term.hole "_")])) [])
              (group (Tactic.exact "exact" (Term.app `hν [(Term.hole "_")])) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d_Inter []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α])))])]
             ","
             (Term.arrow
              (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `s [`n])]))
              "→"
              (Term.arrow
               (Term.forall
                "∀"
                [(Term.simpleBinder [`n `m] [])]
                ","
                (Term.arrow
                 («term_≤_» `n "≤" `m)
                 "→"
                 (Init.Core.«term_⊆_» (Term.app `s [`m]) " ⊆ " (Term.app `s [`n]))))
               "→"
               (Term.app
                `tendsto
                [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `s [`n])])))
                 `at_top
                 (Term.app
                  (Topology.Basic.term𝓝 "𝓝")
                  [(Term.app
                    `d
                    [(Set.Data.Set.Lattice.«term⋂_,_»
                      "⋂"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                      ", "
                      (Term.app `s [`n]))])])])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`s `hs `hm]) [])
              (group
               (Tactic.«tactic_<;>_»
                (Tactic.refine' "refine'" (Term.app `tendsto.sub [(Term.hole "_") (Term.hole "_")]))
                "<;>"
                (Tactic.refine'
                 "refine'"
                 («term_$__»
                  (Term.proj `Nnreal.tendsto_coe "." (fieldIdx "2"))
                  "$"
                  («term_$__»
                   (Term.proj («term_$__» `Ennreal.tendsto_to_nnreal "$" (Term.hole "_")) "." `comp)
                   "$"
                   (Term.app `tendsto_measure_Inter [`hs `hm (Term.hole "_")])))))
               [])
              (group
               (exacts
                "exacts"
                "["
                [(Term.app `hμ [(Term.hole "_")])
                 ","
                 (Term.anonymousCtor "⟨" [(numLit "0") "," (Term.app `hμ [(Term.hole "_")])] "⟩")
                 ","
                 (Term.app `hν [(Term.hole "_")])
                 ","
                 (Term.anonymousCtor "⟨" [(numLit "0") "," (Term.app `hν [(Term.hole "_")])] "⟩")]
                "]")
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`bdd_c []]
          [(Term.typeSpec ":" (Term.app `BddAbove [`c]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.use "use" [(Term.proj (Term.app `μ [`univ]) "." `toNnreal)]) [])
              (group
               (Tactic.rintro
                "rintro"
                [(Tactic.rintroPat.one (Tactic.rcasesPat.one `r))
                 (Tactic.rintroPat.one
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                   "⟩"))]
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `le_transₓ
                 [(«term_$__»
                   (Term.app `sub_le_self [(Term.hole "_")])
                   "$"
                   (Term.app `Nnreal.coe_nonneg [(Term.hole "_")]))
                  (Term.hole "_")]))
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Nnreal.coe_le_coe)
                  ","
                  (Tactic.rwRule ["←"] `Ennreal.coe_le_coe)
                  ","
                  (Tactic.rwRule [] `to_nnreal_μ)
                  ","
                  (Tactic.rwRule [] `to_nnreal_μ)]
                 "]")
                [])
               [])
              (group
               (Tactic.exact "exact" (Term.app `measure_mono [(Term.app `subset_univ [(Term.hole "_")])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`c_nonempty []]
          [(Term.typeSpec ":" `c.nonempty)]
          ":="
          (Term.app
           `nonempty.image
           [(Term.hole "_") (Term.anonymousCtor "⟨" [(Term.hole "_") "," `MeasurableSet.empty] "⟩")]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`d_le_γ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [])]
             ","
             (Term.arrow (Term.app `MeasurableSet [`s]) "→" («term_≤_» (Term.app `d [`s]) "≤" `γ))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `hs] [])]
            "=>"
            (Term.app `le_cSup [`bdd_c (Term.anonymousCtor "⟨" [`s "," `hs "," `rfl] "⟩")]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders [(Lean.binderIdent `s)] [":" (Term.app `Set [`α])]))
              ","
              («term_∧_»
               (Term.app `MeasurableSet [`s])
               "∧"
               («term_<_»
                («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
                "<"
                (Term.app `d [`s]))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec
                    ":"
                    («term_<_» («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)) "<" `γ))]
                  ":="
                  (Term.app `sub_lt_self [`γ (Term.app `pow_pos [(Term.app `half_pos [`zero_lt_one]) `n])]))))
               [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] (Term.app `exists_lt_of_lt_cSup [`c_nonempty `this]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
                   ","
                   (Tactic.rcasesPatLo
                    (Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                       "⟩")])
                    [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hlt)]) [])]
                  "⟩")])
               [])
              (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`s "," `hs "," `hlt] "⟩")) [])]))))))
       [])
      (group
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `Classical.axiom_of_choice [`this]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `e)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `he)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.change
        "change"
        (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α]))
        [(Tactic.location "at" (Tactic.locationHyp [`e] []))])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`he₁ []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`n] [])] "," (Term.app `MeasurableSet [(Term.app `e [`n])])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `he [`n]) "." (fieldIdx "1")))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`he₂ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             («term_<_»
              («term_-_» `γ "-" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
              "<"
              (Term.app `d [(Term.app `e [`n])]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.proj (Term.app `he [`n]) "." (fieldIdx "2")))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `f
          [(Term.typeSpec ":" (Term.arrow (termℕ "ℕ") "→" (Term.arrow (termℕ "ℕ") "→" (Term.app `Set [`α]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`n `m] [])]
            "=>"
            (Term.app
             (Term.proj (Term.app `Finset.ico [`n (Init.Logic.«term_+_» `m "+" (numLit "1"))]) "." `inf)
             [`e]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hf []]
          [(Term.typeSpec
            ":"
            (Term.forall "∀" [(Term.simpleBinder [`n `m] [])] "," (Term.app `MeasurableSet [(Term.app `f [`n `m])])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `m]) [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] [] `f) "," (Tactic.simpLemma [] [] `Finset.inf_eq_infi)] "]"]
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `MeasurableSet.bInter
                 [(Term.app `countable_encodable [(Term.hole "_")])
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`i (Term.hole "_")] [])]
                    "=>"
                    (Term.app `he₁ [(Term.hole "_")])))]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`f_subset_f []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.implicitBinder "{" [`a `b `c `d] [] "}")]
             ","
             (Term.arrow
              («term_≤_» `a "≤" `b)
              "→"
              (Term.arrow
               («term_≤_» `c "≤" `d)
               "→"
               (Init.Core.«term_⊆_» (Term.app `f [`a `d]) " ⊆ " (Term.app `f [`b `c]))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`a `b `c `d `hab `hcd]) [])
              (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] [] []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Finset.inf_eq_infi) "," (Tactic.rwRule [] `Finset.inf_eq_infi)]
                 "]")
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `bInter_subset_bInter_left
                 [(«term_$__» (Term.app `Finset.Ico_subset_Ico [`hab]) "$" (Term.app `Nat.succ_le_succₓ [`hcd]))]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`f_succ []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n `m] [])]
             ","
             (Term.arrow
              («term_≤_» `n "≤" `m)
              "→"
              («term_=_»
               (Term.app `f [`n (Init.Logic.«term_+_» `m "+" (numLit "1"))])
               "="
               (Init.Core.«term_∩_»
                (Term.app `f [`n `m])
                " ∩ "
                (Term.app `e [(Init.Logic.«term_+_» `m "+" (numLit "1"))]))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `m `hnm]) [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  []
                  [(Term.typeSpec ":" («term_≤_» `n "≤" (Init.Logic.«term_+_» `m "+" (numLit "1"))))]
                  ":="
                  (Term.app `le_of_ltₓ [(Term.app `Nat.succ_le_succₓ [`hnm])]))))
               [])
              (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] []) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `Nat.Ico_succ_right_eq_insert_Ico [`this]))
                  ","
                  (Tactic.rwRule [] `Finset.inf_insert)
                  ","
                  (Tactic.rwRule [] `Set.inter_comm)]
                 "]")
                [])
               [])
              (group (Tactic.tacticRfl "rfl") [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`le_d_f []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n `m] [])]
             ","
             (Term.arrow
              («term_≤_» `m "≤" `n)
              "→"
              («term_≤_»
               (Init.Logic.«term_+_»
                («term_-_»
                 `γ
                 "-"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (numLit "2")
                  "*"
                  («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                "+"
                («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))
               "≤"
               (Term.app `d [(Term.app `f [`m `n])])))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `m `h]) [])
              (group (Tactic.refine' "refine'" (Term.app `Nat.le_induction [(Term.hole "_") (Term.hole "_") `n `h])) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.tacticHave_ "have" (Term.haveDecl (Term.haveIdDecl [] [] ":=" (Term.app `he₂ [`m]))))
                    [])
                   (group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `f)] "]"] []) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `Nat.Ico_succ_singleton) "," (Tactic.rwRule [] `Finset.inf_singleton)]
                      "]")
                     [])
                    [])
                   (group (Tactic.exact "exact" (Term.app `aux [`this])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.intro
                     "intro"
                     [`n (Term.paren "(" [`hmn [(Term.typeAscription ":" («term_≤_» `m "≤" `n))]] ")") `ih])
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       []
                       [(Term.typeSpec
                         ":"
                         («term_≤_»
                          (Init.Logic.«term_+_»
                           `γ
                           "+"
                           (Init.Logic.«term_+_»
                            («term_-_»
                             `γ
                             "-"
                             (Finset.Data.Finset.Fold.«term_*_»
                              (numLit "2")
                              "*"
                              («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                            "+"
                            («term_^_»
                             («term_/_» (numLit "1") "/" (numLit "2"))
                             "^"
                             (Init.Logic.«term_+_» `n "+" (numLit "1")))))
                          "≤"
                          (Init.Logic.«term_+_»
                           `γ
                           "+"
                           (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])]))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (tacticCalc_
                             "calc"
                             [(calcStep
                               («term_≤_»
                                (Init.Logic.«term_+_»
                                 `γ
                                 "+"
                                 (Init.Logic.«term_+_»
                                  («term_-_»
                                   `γ
                                   "-"
                                   (Finset.Data.Finset.Fold.«term_*_»
                                    (numLit "2")
                                    "*"
                                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                  "+"
                                  («term_^_»
                                   («term_/_» (numLit "1") "/" (numLit "2"))
                                   "^"
                                   (Init.Logic.«term_+_» `n "+" (numLit "1")))))
                                "≤"
                                (Init.Logic.«term_+_»
                                 `γ
                                 "+"
                                 (Init.Logic.«term_+_»
                                  («term_-_»
                                   `γ
                                   "-"
                                   (Finset.Data.Finset.Fold.«term_*_»
                                    (numLit "2")
                                    "*"
                                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                  "+"
                                  («term_-_»
                                   («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n)
                                   "-"
                                   («term_^_»
                                    («term_/_» (numLit "1") "/" (numLit "2"))
                                    "^"
                                    (Init.Logic.«term_+_» `n "+" (numLit "1")))))))
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.refine'
                                     "refine'"
                                     (Term.app
                                      `add_le_add_left
                                      [(Term.app `add_le_add_left [(Term.hole "_") (Term.hole "_")]) `γ]))
                                    [])
                                   (group
                                    (Tactic.simp
                                     "simp"
                                     []
                                     ["only"]
                                     ["["
                                      [(Tactic.simpLemma [] [] `pow_addₓ)
                                       ","
                                       (Tactic.simpLemma [] [] `pow_oneₓ)
                                       ","
                                       (Tactic.simpLemma [] [] `le_sub_iff_add_le)]
                                      "]"]
                                     [])
                                    [])
                                   (group (Tactic.linarith "linarith" [] [] []) [])]))))
                              (calcStep
                               («term_=_»
                                (Term.hole "_")
                                "="
                                (Init.Logic.«term_+_»
                                 («term_-_»
                                  `γ
                                  "-"
                                  («term_^_»
                                   («term_/_» (numLit "1") "/" (numLit "2"))
                                   "^"
                                   (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                                 "+"
                                 (Init.Logic.«term_+_»
                                  («term_-_»
                                   `γ
                                   "-"
                                   (Finset.Data.Finset.Fold.«term_*_»
                                    (numLit "2")
                                    "*"
                                    («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                                  "+"
                                  («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `n))))
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.«tactic_<;>_»
                                     (Tactic.simp
                                      "simp"
                                      []
                                      ["only"]
                                      ["[" [(Tactic.simpLemma [] [] `sub_eq_add_neg)] "]"]
                                      [])
                                     "<;>"
                                     (Tactic.acRfl "ac_rfl"))
                                    [])]))))
                              (calcStep
                               («term_≤_»
                                (Term.hole "_")
                                "≤"
                                (Init.Logic.«term_+_»
                                 (Term.app `d [(Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
                                 "+"
                                 (Term.app `d [(Term.app `f [`m `n])])))
                               ":="
                               (Term.app
                                `add_le_add
                                [(«term_$__» `le_of_ltₓ "$" (Term.app `he₂ [(Term.hole "_")])) `ih]))
                              (calcStep
                               («term_≤_»
                                (Term.hole "_")
                                "≤"
                                (Init.Logic.«term_+_»
                                 (Init.Logic.«term_+_»
                                  (Term.app `d [(Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])])
                                  "+"
                                  (Term.app
                                   `d
                                   [(Init.Core.«term_\_»
                                     (Term.app `f [`m `n])
                                     " \\ "
                                     (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))]))]))
                                 "+"
                                 (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.rwSeq
                                     "rw"
                                     []
                                     (Tactic.rwRuleSeq
                                      "["
                                      [(Tactic.rwRule [] (Term.app `f_succ [(Term.hole "_") (Term.hole "_") `hmn]))
                                       ","
                                       (Tactic.rwRule
                                        []
                                        (Term.app
                                         `d_split
                                         [(Term.app `f [`m `n])
                                          (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                          (Term.app `hf [(Term.hole "_") (Term.hole "_")])
                                          (Term.app `he₁ [(Term.hole "_")])]))
                                       ","
                                       (Tactic.rwRule [] `add_assocₓ)]
                                      "]")
                                     [])
                                    [])]))))
                              (calcStep
                               («term_=_»
                                (Term.hole "_")
                                "="
                                (Init.Logic.«term_+_»
                                 (Term.app
                                  `d
                                  [(Init.Core.«term_∪_»
                                    (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                    " ∪ "
                                    (Term.app `f [`m `n]))])
                                 "+"
                                 (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                               ":="
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(group
                                    (Tactic.rwSeq
                                     "rw"
                                     []
                                     (Tactic.rwRuleSeq
                                      "["
                                      [(Tactic.rwRule
                                        []
                                        (Term.app
                                         `d_split
                                         [(Init.Core.«term_∪_»
                                           (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                                           " ∪ "
                                           (Term.app `f [`m `n]))
                                          (Term.app `e [(Init.Logic.«term_+_» `n "+" (numLit "1"))])]))
                                       ","
                                       (Tactic.rwRule [] `union_diff_left)
                                       ","
                                       (Tactic.rwRule [] `union_inter_cancel_left)]
                                      "]")
                                     [])
                                    [])
                                   (group (Tactic.acRfl "ac_rfl") [])
                                   (group
                                    (Tactic.exact
                                     "exact"
                                     (Term.app
                                      (Term.proj (Term.app `he₁ [(Term.hole "_")]) "." `union)
                                      [(Term.app `hf [(Term.hole "_") (Term.hole "_")])]))
                                    [])
                                   (group (Tactic.exact "exact" (Term.app `he₁ [(Term.hole "_")])) [])]))))
                              (calcStep
                               («term_≤_»
                                (Term.hole "_")
                                "≤"
                                (Init.Logic.«term_+_»
                                 `γ
                                 "+"
                                 (Term.app `d [(Term.app `f [`m (Init.Logic.«term_+_» `n "+" (numLit "1"))])])))
                               ":="
                               (Term.app
                                `add_le_add_right
                                [(«term_$__»
                                  (Term.app `d_le_γ [(Term.hole "_")])
                                  "$"
                                  (Term.app
                                   (Term.proj (Term.app `he₁ [(Term.hole "_")]) "." `union)
                                   [(Term.app `hf [(Term.hole "_") (Term.hole "_")])]))
                                 (Term.hole "_")]))])
                            [])]))))))
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1")) [`this]))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `s
          []
          ":="
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
           ", "
           (Set.Data.Set.Lattice.«term⋂_,_»
            "⋂"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
            ", "
            (Term.app `f [`m `n]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`γ_le_d_s []]
          [(Term.typeSpec ":" («term_≤_» `γ "≤" (Term.app `d [`s])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hγ []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `tendsto
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                        "=>"
                        («term_-_»
                         `γ
                         "-"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "2")
                          "*"
                          («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                      `at_top
                      (Term.app (Topology.Basic.term𝓝 "𝓝") [`γ])]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.tacticSuffices_
                        "suffices"
                        (Term.sufficesDecl
                         []
                         (Term.app
                          `tendsto
                          [(Term.fun
                            "fun"
                            (Term.basicFun
                             [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                             "=>"
                             («term_-_»
                              `γ
                              "-"
                              (Finset.Data.Finset.Fold.«term_*_»
                               (numLit "2")
                               "*"
                               («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                           `at_top
                           (Term.app
                            (Topology.Basic.term𝓝 "𝓝")
                            [(«term_-_» `γ "-" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (numLit "0")))])])
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))
                       [])
                      (group
                       (Tactic.exact
                        "exact"
                        («term_$__»
                         `tendsto_const_nhds.sub
                         "$"
                         («term_$__»
                          `tendsto_const_nhds.mul
                          "$"
                          (Term.app
                           `tendsto_pow_at_top_nhds_0_of_lt_1
                           [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one))
                            (Term.app `half_lt_self [`zero_lt_one])]))))
                       [])]))))))
               [])
              (group
               (Tactic.tacticHave_
                "have"
                (Term.haveDecl
                 (Term.haveIdDecl
                  [`hd []]
                  [(Term.typeSpec
                    ":"
                    (Term.app
                     `tendsto
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`m] [])]
                        "=>"
                        (Term.app
                         `d
                         [(Set.Data.Set.Lattice.«term⋂_,_»
                           "⋂"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                           ", "
                           (Term.app `f [`m `n]))])))
                      `at_top
                      (Term.app
                       (Topology.Basic.term𝓝 "𝓝")
                       [(Term.app
                         `d
                         [(Set.Data.Set.Lattice.«term⋃_,_»
                           "⋃"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
                           ", "
                           (Set.Data.Set.Lattice.«term⋂_,_»
                            "⋂"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                            ", "
                            (Term.app `f [`m `n])))])])]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.refine' "refine'" (Term.app `d_Union [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`n]) [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `MeasurableSet.Inter
                              [(Term.fun
                                "fun"
                                (Term.basicFun
                                 [(Term.simpleBinder [`m] [])]
                                 "=>"
                                 (Term.app `hf [(Term.hole "_") (Term.hole "_")])))]))
                            [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.exact
                             "exact"
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [(Term.simpleBinder [`n `m `hnm] [])]
                               "=>"
                               (Term.app
                                `subset_Inter
                                [(Term.fun
                                  "fun"
                                  (Term.basicFun
                                   [(Term.simpleBinder [`i] [])]
                                   "=>"
                                   («term_$__»
                                    (Term.app `subset.trans [(Term.app `Inter_subset [(Term.app `f [`n]) `i])])
                                    "$"
                                    («term_$__»
                                     (Term.app `f_subset_f [`hnm])
                                     "$"
                                     (Term.app `le_reflₓ [(Term.hole "_")])))))]))))
                            [])])))
                       [])]))))))
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `le_of_tendsto_of_tendsto'
                 [`hγ `hd (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.hole "_")))]))
               [])
              (group
               (Tactic.tacticHave_
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
                       (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
                      `at_top
                      (Term.app
                       (Topology.Basic.term𝓝 "𝓝")
                       [(Term.app
                         `d
                         [(Set.Data.Set.Lattice.«term⋂_,_»
                           "⋂"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                           ", "
                           (Term.app `f [`m `n]))])])]))]
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`n]) [])
                           (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
                       [])
                      (group
                       (Tactic.«tactic·._»
                        "·"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group (Tactic.intro "intro" [`n `m `hnm]) [])
                           (group
                            (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm]))
                            [])])))
                       [])]))))))
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `ge_of_tendsto
                 [`this
                  (Term.app
                   (Term.proj `eventually_at_top "." (fieldIdx "2"))
                   [(Term.anonymousCtor
                     "⟨"
                     [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
                     "⟩")])]))
               [])
              (group
               (Tactic.change
                "change"
                («term_≤_»
                 («term_-_»
                  `γ
                  "-"
                  (Finset.Data.Finset.Fold.«term_*_»
                   (numLit "2")
                   "*"
                   («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
                 "≤"
                 (Term.app `d [(Term.app `f [`m `n])]))
                [])
               [])
              (group
               (Tactic.refine'
                "refine'"
                (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])]))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `le_add_of_le_of_nonneg
                 [(Term.app `le_reflₓ [(Term.hole "_")])
                  (Term.app
                   `pow_nonneg
                   [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hs []]
          [(Term.typeSpec ":" (Term.app `MeasurableSet [`s]))]
          ":="
          (Term.app
           `MeasurableSet.Union
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`n] [])]
              "=>"
              (Term.app
               `MeasurableSet.Inter
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`m] [])]
                  "=>"
                  (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])))]))))
       [])
      (group
       (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_") "," (Term.hole "_")] "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`t `ht `hts]) [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `d [`t])))]
               ":="
               («term_$__»
                (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
                "$"
                (calc
                 "calc"
                 [(calcStep
                   («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.«tactic_<;>_»
                         (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                         "<;>"
                         (Tactic.exact "exact" `γ_le_d_s))
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Tactic.rwSeq
                         "rw"
                         []
                         (Tactic.rwRuleSeq
                          "["
                          [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
                           ","
                           (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
                          "]")
                         [])
                        [])]))))
                  (calcStep
                   («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
                   ":="
                   (Term.app
                    `add_le_add
                    [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])])
                     (Term.app `le_reflₓ [(Term.hole "_")])]))])))))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `to_nnreal_μ)
               ","
               (Tactic.rwRule ["←"] `to_nnreal_ν)
               ","
               (Tactic.rwRule [] `Ennreal.coe_le_coe)
               ","
               (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
              "]")
             [])
            [])
           (group
            (Tactic.simpa
             "simpa"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `d)
               ","
               (Tactic.simpLemma [] [] `le_sub_iff_add_le)
               ","
               (Tactic.simpLemma [] [] `zero_addₓ)]
              "]"]
             []
             ["using" `this])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`t `ht `hts]) [])
           (group (Tactic.have'' "have" [] [(Term.typeSpec ":" («term_≤_» (Term.app `d [`t]) "≤" (numLit "0")))]) [])
           (group
            (Tactic.exact
             "exact"
             («term_$__»
              (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
              "$"
              (calc
               "calc"
               [(calcStep
                 («term_≤_»
                  (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
                  "≤"
                  (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
                 ":="
                 (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
                (calcStep
                 («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule
                          []
                          (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
                         ","
                         (Tactic.rwRule [] `union_diff_right)
                         ","
                         (Tactic.rwRule [] `union_inter_cancel_right)
                         ","
                         (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
                        "]")
                       [])
                      [])
                     (group
                      (Tactic.exact
                       "exact"
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
                         "=>"
                         (Term.app `hts [`hat `has]))))
                      [])]))))
                (calcStep
                 («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
                 ":="
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.«tactic_<;>_»
                       (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                       "<;>"
                       (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
                      [])]))))])))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule ["←"] `to_nnreal_μ)
               ","
               (Tactic.rwRule ["←"] `to_nnreal_ν)
               ","
               (Tactic.rwRule [] `Ennreal.coe_le_coe)
               ","
               (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
              "]")
             [])
            [])
           (group
            (Tactic.simpa
             "simpa"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `d)
               ","
               (Tactic.simpLemma [] [] `sub_le_iff_le_add)
               ","
               (Tactic.simpLemma [] [] `zero_addₓ)]
              "]"]
             []
             ["using" `this])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`t `ht `hts]) [])
      (group (Tactic.have'' "have" [] [(Term.typeSpec ":" («term_≤_» (Term.app `d [`t]) "≤" (numLit "0")))]) [])
      (group
       (Tactic.exact
        "exact"
        («term_$__»
         (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
         "$"
         (calc
          "calc"
          [(calcStep
            («term_≤_»
             (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
             "≤"
             (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
            ":="
            (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
           (calcStep
            («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule
                     []
                     (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
                    ","
                    (Tactic.rwRule [] `union_diff_right)
                    ","
                    (Tactic.rwRule [] `union_inter_cancel_right)
                    ","
                    (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.exact
                  "exact"
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
                    "=>"
                    (Term.app `hts [`hat `has]))))
                 [])]))))
           (calcStep
            («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
            ":="
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.«tactic_<;>_»
                  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                  "<;>"
                  (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
                 [])]))))])))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `to_nnreal_μ)
          ","
          (Tactic.rwRule ["←"] `to_nnreal_ν)
          ","
          (Tactic.rwRule [] `Ennreal.coe_le_coe)
          ","
          (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
         "]")
        [])
       [])
      (group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `d)
          ","
          (Tactic.simpLemma [] [] `sub_le_iff_le_add)
          ","
          (Tactic.simpLemma [] [] `zero_addₓ)]
         "]"]
        []
        ["using" `this])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `d)
     ","
     (Tactic.simpLemma [] [] `sub_le_iff_le_add)
     ","
     (Tactic.simpLemma [] [] `zero_addₓ)]
    "]"]
   []
   ["using" `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_addₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_le_iff_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `to_nnreal_μ)
     ","
     (Tactic.rwRule ["←"] `to_nnreal_ν)
     ","
     (Tactic.rwRule [] `Ennreal.coe_le_coe)
     ","
     (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_le_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ennreal.coe_le_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_nnreal_ν
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_nnreal_μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.exact
   "exact"
   («term_$__»
    (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
    "$"
    (calc
     "calc"
     [(calcStep
       («term_≤_»
        (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
        "≤"
        (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
       ":="
       (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
      (calcStep
       («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
               ","
               (Tactic.rwRule [] `union_diff_right)
               ","
               (Tactic.rwRule [] `union_inter_cancel_right)
               ","
               (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
              "]")
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
               "=>"
               (Term.app `hts [`hat `has]))))
            [])]))))
      (calcStep
       («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic_<;>_»
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
             "<;>"
             (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
            [])]))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
   "$"
   (calc
    "calc"
    [(calcStep
      («term_≤_»
       (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
       "≤"
       (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
      ":="
      (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
     (calcStep
      («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
              ","
              (Tactic.rwRule [] `union_diff_right)
              ","
              (Tactic.rwRule [] `union_inter_cancel_right)
              ","
              (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
             "]")
            [])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
              "=>"
              (Term.app `hts [`hat `has]))))
           [])]))))
     (calcStep
      («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
            "<;>"
            (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
           [])]))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_≤_»
      (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
      "≤"
      (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
     ":="
     (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])]))
    (calcStep
     («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
             ","
             (Tactic.rwRule [] `union_diff_right)
             ","
             (Tactic.rwRule [] `union_inter_cancel_right)
             ","
             (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
            "]")
           [])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
             "=>"
             (Term.app `hts [`hat `has]))))
          [])]))))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
           "<;>"
           (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
        "<;>"
        (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
   "<;>"
   (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.union [`ht])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hs.union [`ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hs.union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hs.union [`ht]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d_le_γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_zeroₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `γ "+" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
          ","
          (Tactic.rwRule [] `union_diff_right)
          ","
          (Tactic.rwRule [] `union_inter_cancel_right)
          ","
          (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
          "=>"
          (Term.app `hts [`hat `has]))))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.fun
    "fun"
    (Term.basicFun
     [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
     "=>"
     (Term.app `hts [`hat `has]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`a] []) (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")]
    "=>"
    (Term.app `hts [`hat `has])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hts [`hat `has])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `has
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hat
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.simpleBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`hat "," `has] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `has
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hat
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht]))
     ","
     (Tactic.rwRule [] `union_diff_right)
     ","
     (Tactic.rwRule [] `union_inter_cancel_right)
     ","
     (Tactic.rwRule [] (Term.proj `diff_eq_self "." (fieldIdx "2")))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `diff_eq_self "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `diff_eq_self
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `union_inter_cancel_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `union_diff_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d_split [(Term.hole "_") (Term.hole "_") (Term.app `hs.union [`ht]) `ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hs.union [`ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hs.union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hs.union [`ht]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d_split
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [(Init.Core.«term_∪_» `s " ∪ " `t)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∪_» `s " ∪ " `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∪_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 65, (some 66, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Core.«term_∪_» `s " ∪ " `t) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.app `add_le_add [`γ_le_d_s (Term.app `le_reflₓ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_reflₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `γ_le_d_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
   "≤"
   (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `d [`s]) "+" (Term.app `d [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `d [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `add_le_add_iff_left [`γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add_iff_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `add_le_add_iff_left [`γ]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.have'' "have" [] [(Term.typeSpec ":" («term_≤_» (Term.app `d [`t]) "≤" (numLit "0")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.have''', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `d [`t]) "≤" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`t `ht `hts])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`t `ht `hts]) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `d [`t])))]
          ":="
          («term_$__»
           (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
           "$"
           (calc
            "calc"
            [(calcStep
              («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.«tactic_<;>_»
                    (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
                    "<;>"
                    (Tactic.exact "exact" `γ_le_d_s))
                   [])]))))
             (calcStep
              («term_=_»
               (Term.hole "_")
               "="
               (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq
                     "["
                     [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
                      ","
                      (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
                     "]")
                    [])
                   [])]))))
             (calcStep
              («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
              ":="
              (Term.app
               `add_le_add
               [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])])
                (Term.app `le_reflₓ [(Term.hole "_")])]))])))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] `to_nnreal_μ)
          ","
          (Tactic.rwRule ["←"] `to_nnreal_ν)
          ","
          (Tactic.rwRule [] `Ennreal.coe_le_coe)
          ","
          (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
         "]")
        [])
       [])
      (group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `d)
          ","
          (Tactic.simpLemma [] [] `le_sub_iff_add_le)
          ","
          (Tactic.simpLemma [] [] `zero_addₓ)]
         "]"]
        []
        ["using" `this])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simpa
   "simpa"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `d)
     ","
     (Tactic.simpLemma [] [] `le_sub_iff_add_le)
     ","
     (Tactic.simpLemma [] [] `zero_addₓ)]
    "]"]
   []
   ["using" `this])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_addₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `le_sub_iff_add_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] `to_nnreal_μ)
     ","
     (Tactic.rwRule ["←"] `to_nnreal_ν)
     ","
     (Tactic.rwRule [] `Ennreal.coe_le_coe)
     ","
     (Tactic.rwRule ["←"] `Nnreal.coe_le_coe)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Nnreal.coe_le_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Ennreal.coe_le_coe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_nnreal_ν
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `to_nnreal_μ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `d [`t])))]
     ":="
     («term_$__»
      (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
      "$"
      (calc
       "calc"
       [(calcStep
         («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.«tactic_<;>_»
               (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
               "<;>"
               (Tactic.exact "exact" `γ_le_d_s))
              [])]))))
        (calcStep
         («term_=_»
          (Term.hole "_")
          "="
          (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
         ":="
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
                 ","
                 (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
                "]")
               [])
              [])]))))
        (calcStep
         («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
         ":="
         (Term.app
          `add_le_add
          [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])])
           (Term.app `le_reflₓ [(Term.hole "_")])]))])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
   "$"
   (calc
    "calc"
    [(calcStep
      («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.«tactic_<;>_»
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
            "<;>"
            (Tactic.exact "exact" `γ_le_d_s))
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
              ","
              (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
             "]")
            [])
           [])]))))
     (calcStep
      («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
      ":="
      (Term.app
       `add_le_add
       [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])]) (Term.app `le_reflₓ [(Term.hole "_")])]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.«tactic_<;>_»
           (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
           "<;>"
           (Tactic.exact "exact" `γ_le_d_s))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
             ","
             (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
            "]")
           [])
          [])]))))
    (calcStep
     («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
     ":="
     (Term.app
      `add_le_add
      [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])]) (Term.app `le_reflₓ [(Term.hole "_")])]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `add_le_add
   [(Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])]) (Term.app `le_reflₓ [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_reflₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `d_le_γ [(Term.hole "_") (Term.app `hs.diff [`ht])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hs.diff [`ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hs.diff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hs.diff [`ht]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d_le_γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `d_le_γ [(Term.hole "_") (Term.paren "(" [(Term.app `hs.diff [`ht]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `γ "+" (Term.app `d [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
          ","
          (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht]))
     ","
     (Tactic.rwRule [] (Term.app `inter_eq_self_of_subset_right [`hts]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `inter_eq_self_of_subset_right [`hts])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `inter_eq_self_of_subset_right
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d_split [(Term.hole "_") (Term.hole "_") `hs `ht])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d_split
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)]) "+" (Term.app `d [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `d [(Init.Core.«term_\_» `s " \\ " `t)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_\_» `s " \\ " `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_\_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 70, (some 71, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Core.«term_\_» `s " \\ " `t) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.«tactic_<;>_»
        (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
        "<;>"
        (Tactic.exact "exact" `γ_le_d_s))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
   "<;>"
   (Tactic.exact "exact" `γ_le_d_s))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `γ_le_d_s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ_le_d_s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `add_zeroₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_zeroₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Init.Logic.«term_+_» `γ "+" (numLit "0")) "≤" (Term.app `d [`s]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `γ "+" (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `γ "+" (numLit "0")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `add_le_add_iff_left [`γ]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `add_le_add_iff_left [`γ])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `add_le_add_iff_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `add_le_add_iff_left [`γ]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (numLit "0") "≤" (Term.app `d [`t]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [`t])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`t `ht `hts])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hts
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ht
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_") "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_") "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`hs []]
     [(Term.typeSpec ":" (Term.app `MeasurableSet [`s]))]
     ":="
     (Term.app
      `MeasurableSet.Union
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`n] [])]
         "=>"
         (Term.app
          `MeasurableSet.Inter
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`m] [])]
             "=>"
             (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])))]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `MeasurableSet.Union
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n] [])]
      "=>"
      (Term.app
       `MeasurableSet.Inter
       [(Term.fun
         "fun"
         (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`n] [])]
    "=>"
    (Term.app
     `MeasurableSet.Inter
     [(Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `MeasurableSet.Inter
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.app `hf [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.app `hf [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MeasurableSet.Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MeasurableSet.Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `MeasurableSet [`s])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MeasurableSet
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`γ_le_d_s []]
     [(Term.typeSpec ":" («term_≤_» `γ "≤" (Term.app `d [`s])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hγ []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                   "=>"
                   («term_-_»
                    `γ
                    "-"
                    (Finset.Data.Finset.Fold.«term_*_»
                     (numLit "2")
                     "*"
                     («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                 `at_top
                 (Term.app (Topology.Basic.term𝓝 "𝓝") [`γ])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.tacticSuffices_
                   "suffices"
                   (Term.sufficesDecl
                    []
                    (Term.app
                     `tendsto
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                        "=>"
                        («term_-_»
                         `γ
                         "-"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (numLit "2")
                          "*"
                          («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                      `at_top
                      (Term.app
                       (Topology.Basic.term𝓝 "𝓝")
                       [(«term_-_» `γ "-" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (numLit "0")))])])
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))
                  [])
                 (group
                  (Tactic.exact
                   "exact"
                   («term_$__»
                    `tendsto_const_nhds.sub
                    "$"
                    («term_$__»
                     `tendsto_const_nhds.mul
                     "$"
                     (Term.app
                      `tendsto_pow_at_top_nhds_0_of_lt_1
                      [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one))
                       (Term.app `half_lt_self [`zero_lt_one])]))))
                  [])]))))))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`hd []]
             [(Term.typeSpec
               ":"
               (Term.app
                `tendsto
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`m] [])]
                   "=>"
                   (Term.app
                    `d
                    [(Set.Data.Set.Lattice.«term⋂_,_»
                      "⋂"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                      ", "
                      (Term.app `f [`m `n]))])))
                 `at_top
                 (Term.app
                  (Topology.Basic.term𝓝 "𝓝")
                  [(Term.app
                    `d
                    [(Set.Data.Set.Lattice.«term⋃_,_»
                      "⋃"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
                      ", "
                      (Set.Data.Set.Lattice.«term⋂_,_»
                       "⋂"
                       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                       ", "
                       (Term.app `f [`m `n])))])])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine' "refine'" (Term.app `d_Union [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`n]) [])
                      (group
                       (Tactic.exact
                        "exact"
                        (Term.app
                         `MeasurableSet.Inter
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`m] [])]
                            "=>"
                            (Term.app `hf [(Term.hole "_") (Term.hole "_")])))]))
                       [])])))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.exact
                        "exact"
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`n `m `hnm] [])]
                          "=>"
                          (Term.app
                           `subset_Inter
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [(Term.simpleBinder [`i] [])]
                              "=>"
                              («term_$__»
                               (Term.app `subset.trans [(Term.app `Inter_subset [(Term.app `f [`n]) `i])])
                               "$"
                               («term_$__»
                                (Term.app `f_subset_f [`hnm])
                                "$"
                                (Term.app `le_reflₓ [(Term.hole "_")])))))]))))
                       [])])))
                  [])]))))))
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `le_of_tendsto_of_tendsto'
            [`hγ `hd (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.tacticHave_
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
                  (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
                 `at_top
                 (Term.app
                  (Topology.Basic.term𝓝 "𝓝")
                  [(Term.app
                    `d
                    [(Set.Data.Set.Lattice.«term⋂_,_»
                      "⋂"
                      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                      ", "
                      (Term.app `f [`m `n]))])])]))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`n]) [])
                      (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.intro "intro" [`n `m `hnm]) [])
                      (group
                       (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm]))
                       [])])))
                  [])]))))))
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `ge_of_tendsto
            [`this
             (Term.app
              (Term.proj `eventually_at_top "." (fieldIdx "2"))
              [(Term.anonymousCtor
                "⟨"
                [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
                "⟩")])]))
          [])
         (group
          (Tactic.change
           "change"
           («term_≤_»
            («term_-_»
             `γ
             "-"
             (Finset.Data.Finset.Fold.«term_*_»
              (numLit "2")
              "*"
              («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
            "≤"
            (Term.app `d [(Term.app `f [`m `n])]))
           [])
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])]))
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `le_add_of_le_of_nonneg
            [(Term.app `le_reflₓ [(Term.hole "_")])
             (Term.app
              `pow_nonneg
              [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])]))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hγ []]
          [(Term.typeSpec
            ":"
            (Term.app
             `tendsto
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                "=>"
                («term_-_»
                 `γ
                 "-"
                 (Finset.Data.Finset.Fold.«term_*_»
                  (numLit "2")
                  "*"
                  («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
              `at_top
              (Term.app (Topology.Basic.term𝓝 "𝓝") [`γ])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.tacticSuffices_
                "suffices"
                (Term.sufficesDecl
                 []
                 (Term.app
                  `tendsto
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                     "=>"
                     («term_-_»
                      `γ
                      "-"
                      (Finset.Data.Finset.Fold.«term_*_»
                       (numLit "2")
                       "*"
                       («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))))
                   `at_top
                   (Term.app
                    (Topology.Basic.term𝓝 "𝓝")
                    [(«term_-_» `γ "-" (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" (numLit "0")))])])
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simpa "simpa" [] [] [] [] []) [])])))))
               [])
              (group
               (Tactic.exact
                "exact"
                («term_$__»
                 `tendsto_const_nhds.sub
                 "$"
                 («term_$__»
                  `tendsto_const_nhds.mul
                  "$"
                  (Term.app
                   `tendsto_pow_at_top_nhds_0_of_lt_1
                   [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one))
                    (Term.app `half_lt_self [`zero_lt_one])]))))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hd []]
          [(Term.typeSpec
            ":"
            (Term.app
             `tendsto
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`m] [])]
                "=>"
                (Term.app
                 `d
                 [(Set.Data.Set.Lattice.«term⋂_,_»
                   "⋂"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                   ", "
                   (Term.app `f [`m `n]))])))
              `at_top
              (Term.app
               (Topology.Basic.term𝓝 "𝓝")
               [(Term.app
                 `d
                 [(Set.Data.Set.Lattice.«term⋃_,_»
                   "⋃"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `m)] []))
                   ", "
                   (Set.Data.Set.Lattice.«term⋂_,_»
                    "⋂"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                    ", "
                    (Term.app `f [`m `n])))])])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine' "refine'" (Term.app `d_Union [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`n]) [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `MeasurableSet.Inter
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`m] [])]
                         "=>"
                         (Term.app `hf [(Term.hole "_") (Term.hole "_")])))]))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`n `m `hnm] [])]
                       "=>"
                       (Term.app
                        `subset_Inter
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`i] [])]
                           "=>"
                           («term_$__»
                            (Term.app `subset.trans [(Term.app `Inter_subset [(Term.app `f [`n]) `i])])
                            "$"
                            («term_$__»
                             (Term.app `f_subset_f [`hnm])
                             "$"
                             (Term.app `le_reflₓ [(Term.hole "_")])))))]))))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `le_of_tendsto_of_tendsto'
         [`hγ `hd (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`m] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.app
             `tendsto
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
              `at_top
              (Term.app
               (Topology.Basic.term𝓝 "𝓝")
               [(Term.app
                 `d
                 [(Set.Data.Set.Lattice.«term⋂_,_»
                   "⋂"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
                   ", "
                   (Term.app `f [`m `n]))])])]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`n]) [])
                   (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`n `m `hnm]) [])
                   (group
                    (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm]))
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `ge_of_tendsto
         [`this
          (Term.app
           (Term.proj `eventually_at_top "." (fieldIdx "2"))
           [(Term.anonymousCtor
             "⟨"
             [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
             "⟩")])]))
       [])
      (group
       (Tactic.change
        "change"
        («term_≤_»
         («term_-_»
          `γ
          "-"
          (Finset.Data.Finset.Fold.«term_*_»
           (numLit "2")
           "*"
           («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
         "≤"
         (Term.app `d [(Term.app `f [`m `n])]))
        [])
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `le_add_of_le_of_nonneg
         [(Term.app `le_reflₓ [(Term.hole "_")])
          (Term.app
           `pow_nonneg
           [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `le_add_of_le_of_nonneg
    [(Term.app `le_reflₓ [(Term.hole "_")])
     (Term.app `pow_nonneg [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `le_add_of_le_of_nonneg
   [(Term.app `le_reflₓ [(Term.hole "_")])
    (Term.app `pow_nonneg [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `pow_nonneg [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  («term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__» `half_pos "$" `zero_lt_one)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_lt_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `half_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  `le_of_ltₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 10, (some 10, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `pow_nonneg
   [(Term.paren "(" [(«term_$__» `le_of_ltₓ "$" («term_$__» `half_pos "$" `zero_lt_one)) []] ")") (Term.hole "_")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `le_reflₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_add_of_le_of_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_transₓ [(Term.hole "_") (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hmn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_d_f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `le_d_f [(Term.hole "_") (Term.hole "_") `hmn]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_transₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_≤_»
    («term_-_»
     `γ
     "-"
     (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
    "≤"
    (Term.app `d [(Term.app `f [`m `n])]))
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   («term_-_»
    `γ
    "-"
    (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
   "≤"
   (Term.app `d [(Term.app `f [`m `n])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d [(Term.app `f [`m `n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`m `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`m `n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  («term_-_»
   `γ
   "-"
   (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_» («term_/_» (numLit "1") "/" (numLit "2")) "^" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  («term_/_» (numLit "1") "/" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1024, (none, [anonymous]) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 81 >? 70, (some 71, term) <=? (some 80, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_/_» (numLit "1") "/" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  `γ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1024, (none, [anonymous]) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 65, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_»
   `γ
   "-"
   (Finset.Data.Finset.Fold.«term_*_»
    (numLit "2")
    "*"
    («term_^_» (Term.paren "(" [(«term_/_» (numLit "1") "/" (numLit "2")) []] ")") "^" `m)))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `ge_of_tendsto
    [`this
     (Term.app
      (Term.proj `eventually_at_top "." (fieldIdx "2"))
      [(Term.anonymousCtor
        "⟨"
        [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
        "⟩")])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `ge_of_tendsto
   [`this
    (Term.app
     (Term.proj `eventually_at_top "." (fieldIdx "2"))
     [(Term.anonymousCtor
       "⟨"
       [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
       "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj `eventually_at_top "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
     "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj `eventually_at_top "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `eventually_at_top
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj `eventually_at_top "." (fieldIdx "2"))
   [(Term.anonymousCtor
     "⟨"
     [`m "," (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n `hmn] [])] "=>" (Term.hole "_")))]
     "⟩")])
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ge_of_tendsto
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       (Term.app
        `tendsto
        [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
         `at_top
         (Term.app
          (Topology.Basic.term𝓝 "𝓝")
          [(Term.app
            `d
            [(Set.Data.Set.Lattice.«term⋂_,_»
              "⋂"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
              ", "
              (Term.app `f [`m `n]))])])]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")])) [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n]) [])
              (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
          [])
         (group
          (Tactic.«tactic·._»
           "·"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`n `m `hnm]) [])
              (group (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm])) [])])))
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")])) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`n]) [])
           (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`n `m `hnm]) [])
           (group (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm])) [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`n `m `hnm]) [])
      (group (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f_subset_f [(Term.app `le_reflₓ [(Term.hole "_")]) `hnm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hnm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `le_reflₓ [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `le_reflₓ [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f_subset_f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`n `m `hnm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hnm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`n]) [])
      (group (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `hf [(Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf [(Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hf
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `d_Inter [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `d_Inter
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `tendsto
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.app `d [(Term.app `f [`m `n])])))
    `at_top
    (Term.app
     (Topology.Basic.term𝓝 "𝓝")
     [(Term.app
       `d
       [(Set.Data.Set.Lattice.«term⋂_,_»
         "⋂"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
         ", "
         (Term.app `f [`m `n]))])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Topology.Basic.term𝓝 "𝓝")
   [(Term.app
     `d
     [(Set.Data.Set.Lattice.«term⋂_,_»
       "⋂"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
       ", "
       (Term.app `f [`m `n]))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `d
   [(Set.Data.Set.Lattice.«term⋂_,_»
     "⋂"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
     ", "
     (Term.app `f [`m `n]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋂_,_»
   "⋂"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `n)] []))
   ", "
   (Term.app `f [`m `n]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋂_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `f [`m `n])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- **Hahn decomposition theorem** -/
  theorem
    hahn_decomposition
    [ is_finite_measure μ ] [ is_finite_measure ν ]
      : ∃ s , MeasurableSet s ∧ ∀ t , MeasurableSet t → t ⊆ s → ν t ≤ μ t ∧ ∀ t , MeasurableSet t → t ⊆ s ᶜ → μ t ≤ ν t
    :=
      by
        let d : Set α → ℝ := fun s => ( μ s . toNnreal : ℝ ) - ν s . toNnreal
          let c : Set ℝ := d '' { s | MeasurableSet s }
          let γ : ℝ := Sup c
          have hμ : ∀ s , μ s ≠ ∞ := measure_ne_top μ
          have hν : ∀ s , ν s ≠ ∞ := measure_ne_top ν
          have to_nnreal_μ : ∀ s , ( μ s . toNnreal : ℝ≥0∞ ) = μ s := fun s => Ennreal.coe_to_nnreal $ hμ _
          have to_nnreal_ν : ∀ s , ( ν s . toNnreal : ℝ≥0∞ ) = ν s := fun s => Ennreal.coe_to_nnreal $ hν _
          have d_empty : d ∅ = 0 := by change _ - _ = _ rw [ measure_empty , measure_empty , sub_self ]
          have
            d_split
              : ∀ s t , MeasurableSet s → MeasurableSet t → d s = d s \ t + d s ∩ t
              :=
              by
                intro s t hs ht
                  simp only [ d ]
                  rw
                    [
                      ← measure_inter_add_diff s ht
                        ,
                        ← measure_inter_add_diff s ht
                        ,
                        Ennreal.to_nnreal_add hμ _ hμ _
                        ,
                        Ennreal.to_nnreal_add hν _ hν _
                        ,
                        Nnreal.coe_add
                        ,
                        Nnreal.coe_add
                      ]
                  simp only [ sub_eq_add_neg , neg_add ]
                  ac_rfl
          have
            d_Union
              : ∀ s : ℕ → Set α , ∀ n , MeasurableSet s n → Monotone s → tendsto fun n => d s n at_top 𝓝 d ⋃ n , s n
              :=
              by
                intro s hs hm
                  refine' tendsto.sub _ _
                    <;>
                    refine' Nnreal.tendsto_coe . 2 $ Ennreal.tendsto_to_nnreal _ . comp $ tendsto_measure_Union hs hm
                  exact hμ _
                  exact hν _
          have
            d_Inter
              :
                ∀
                  s : ℕ → Set α
                  ,
                  ∀ n , MeasurableSet s n → ∀ n m , n ≤ m → s m ⊆ s n → tendsto fun n => d s n at_top 𝓝 d ⋂ n , s n
              :=
              by
                intro s hs hm
                  refine' tendsto.sub _ _
                    <;>
                    refine'
                      Nnreal.tendsto_coe . 2 $ Ennreal.tendsto_to_nnreal $ _ . comp $ tendsto_measure_Inter hs hm _
                  exacts [ hμ _ , ⟨ 0 , hμ _ ⟩ , hν _ , ⟨ 0 , hν _ ⟩ ]
          have
            bdd_c
              : BddAbove c
              :=
              by
                use μ univ . toNnreal
                  rintro r ⟨ s , hs , rfl ⟩
                  refine' le_transₓ sub_le_self _ $ Nnreal.coe_nonneg _ _
                  rw [ Nnreal.coe_le_coe , ← Ennreal.coe_le_coe , to_nnreal_μ , to_nnreal_μ ]
                  exact measure_mono subset_univ _
          have c_nonempty : c.nonempty := nonempty.image _ ⟨ _ , MeasurableSet.empty ⟩
          have d_le_γ : ∀ s , MeasurableSet s → d s ≤ γ := fun s hs => le_cSup bdd_c ⟨ s , hs , rfl ⟩
          have
            : ∀ n : ℕ , ∃ s : Set α , MeasurableSet s ∧ γ - 1 / 2 ^ n < d s
              :=
              by
                intro n
                  have : γ - 1 / 2 ^ n < γ := sub_lt_self γ pow_pos half_pos zero_lt_one n
                  rcases exists_lt_of_lt_cSup c_nonempty this with ⟨ r , ⟨ s , hs , rfl ⟩ , hlt ⟩
                  exact ⟨ s , hs , hlt ⟩
          rcases Classical.axiom_of_choice this with ⟨ e , he ⟩
          change ℕ → Set α at e
          have he₁ : ∀ n , MeasurableSet e n := fun n => he n . 1
          have he₂ : ∀ n , γ - 1 / 2 ^ n < d e n := fun n => he n . 2
          let f : ℕ → ℕ → Set α := fun n m => Finset.ico n m + 1 . inf e
          have
            hf
              : ∀ n m , MeasurableSet f n m
              :=
              by
                intro n m
                  simp only [ f , Finset.inf_eq_infi ]
                  exact MeasurableSet.bInter countable_encodable _ fun i _ => he₁ _
          have
            f_subset_f
              : ∀ { a b c d } , a ≤ b → c ≤ d → f a d ⊆ f b c
              :=
              by
                intro a b c d hab hcd
                  dsimp only [ f ]
                  rw [ Finset.inf_eq_infi , Finset.inf_eq_infi ]
                  exact bInter_subset_bInter_left Finset.Ico_subset_Ico hab $ Nat.succ_le_succₓ hcd
          have
            f_succ
              : ∀ n m , n ≤ m → f n m + 1 = f n m ∩ e m + 1
              :=
              by
                intro n m hnm
                  have : n ≤ m + 1 := le_of_ltₓ Nat.succ_le_succₓ hnm
                  simp only [ f ]
                  rw [ Nat.Ico_succ_right_eq_insert_Ico this , Finset.inf_insert , Set.inter_comm ]
                  rfl
          have
            le_d_f
              : ∀ n m , m ≤ n → γ - 2 * 1 / 2 ^ m + 1 / 2 ^ n ≤ d f m n
              :=
              by
                intro n m h
                  refine' Nat.le_induction _ _ n h
                  · have := he₂ m simp only [ f ] rw [ Nat.Ico_succ_singleton , Finset.inf_singleton ] exact aux this
                  ·
                    intro n ( hmn : m ≤ n ) ih
                      have
                        : γ + γ - 2 * 1 / 2 ^ m + 1 / 2 ^ n + 1 ≤ γ + d f m n + 1
                          :=
                          by
                            calc
                              γ + γ - 2 * 1 / 2 ^ m + 1 / 2 ^ n + 1 ≤ γ + γ - 2 * 1 / 2 ^ m + 1 / 2 ^ n - 1 / 2 ^ n + 1
                                  :=
                                  by
                                    refine' add_le_add_left add_le_add_left _ _ γ
                                      simp only [ pow_addₓ , pow_oneₓ , le_sub_iff_add_le ]
                                      linarith
                                _ = γ - 1 / 2 ^ n + 1 + γ - 2 * 1 / 2 ^ m + 1 / 2 ^ n
                                  :=
                                  by simp only [ sub_eq_add_neg ] <;> ac_rfl
                                _ ≤ d e n + 1 + d f m n := add_le_add le_of_ltₓ $ he₂ _ ih
                                _ ≤ d e n + 1 + d f m n \ e n + 1 + d f m n + 1
                                  :=
                                  by rw [ f_succ _ _ hmn , d_split f m n e n + 1 hf _ _ he₁ _ , add_assocₓ ]
                                _ = d e n + 1 ∪ f m n + d f m n + 1
                                  :=
                                  by
                                    rw [ d_split e n + 1 ∪ f m n e n + 1 , union_diff_left , union_inter_cancel_left ]
                                      ac_rfl
                                      exact he₁ _ . union hf _ _
                                      exact he₁ _
                                _ ≤ γ + d f m n + 1 := add_le_add_right d_le_γ _ $ he₁ _ . union hf _ _ _
                      exact add_le_add_iff_left γ . 1 this
          let s := ⋃ m , ⋂ n , f m n
          have
            γ_le_d_s
              : γ ≤ d s
              :=
              by
                have
                    hγ
                      : tendsto fun m : ℕ => γ - 2 * 1 / 2 ^ m at_top 𝓝 γ
                      :=
                      by
                        suffices tendsto fun m : ℕ => γ - 2 * 1 / 2 ^ m at_top 𝓝 γ - 2 * 0 by simpa
                          exact
                            tendsto_const_nhds.sub
                              $
                              tendsto_const_nhds.mul
                                $
                                tendsto_pow_at_top_nhds_0_of_lt_1
                                  le_of_ltₓ $ half_pos $ zero_lt_one half_lt_self zero_lt_one
                  have
                    hd
                      : tendsto fun m => d ⋂ n , f m n at_top 𝓝 d ⋃ m , ⋂ n , f m n
                      :=
                      by
                        refine' d_Union _ _ _
                          · intro n exact MeasurableSet.Inter fun m => hf _ _
                          ·
                            exact
                              fun
                                n m hnm
                                  =>
                                  subset_Inter fun i => subset.trans Inter_subset f n i $ f_subset_f hnm $ le_reflₓ _
                  refine' le_of_tendsto_of_tendsto' hγ hd fun m => _
                  have
                    : tendsto fun n => d f m n at_top 𝓝 d ⋂ n , f m n
                      :=
                      by refine' d_Inter _ _ _ · intro n exact hf _ _ · intro n m hnm exact f_subset_f le_reflₓ _ hnm
                  refine' ge_of_tendsto this eventually_at_top . 2 ⟨ m , fun n hmn => _ ⟩
                  change γ - 2 * 1 / 2 ^ m ≤ d f m n
                  refine' le_transₓ _ le_d_f _ _ hmn
                  exact le_add_of_le_of_nonneg le_reflₓ _ pow_nonneg le_of_ltₓ $ half_pos $ zero_lt_one _
          have hs : MeasurableSet s := MeasurableSet.Union fun n => MeasurableSet.Inter fun m => hf _ _
          refine' ⟨ s , hs , _ , _ ⟩
          ·
            intro t ht hts
              have
                : 0 ≤ d t
                  :=
                  add_le_add_iff_left γ . 1
                    $
                    calc
                      γ + 0 ≤ d s := by rw [ add_zeroₓ ] <;> exact γ_le_d_s
                        _ = d s \ t + d t := by rw [ d_split _ _ hs ht , inter_eq_self_of_subset_right hts ]
                        _ ≤ γ + d t := add_le_add d_le_γ _ hs.diff ht le_reflₓ _
              rw [ ← to_nnreal_μ , ← to_nnreal_ν , Ennreal.coe_le_coe , ← Nnreal.coe_le_coe ]
              simpa only [ d , le_sub_iff_add_le , zero_addₓ ] using this
          ·
            intro t ht hts
              have : d t ≤ 0
              exact
                add_le_add_iff_left γ . 1
                  $
                  calc
                    γ + d t ≤ d s + d t := add_le_add γ_le_d_s le_reflₓ _
                      _ = d s ∪ t
                        :=
                        by
                          rw
                              [
                                d_split _ _ hs.union ht ht
                                  ,
                                  union_diff_right
                                  ,
                                  union_inter_cancel_right
                                  ,
                                  diff_eq_self . 2
                                ]
                            exact fun a ⟨ hat , has ⟩ => hts hat has
                      _ ≤ γ + 0 := by rw [ add_zeroₓ ] <;> exact d_le_γ _ hs.union ht
              rw [ ← to_nnreal_μ , ← to_nnreal_ν , Ennreal.coe_le_coe , ← Nnreal.coe_le_coe ]
              simpa only [ d , sub_le_iff_le_add , zero_addₓ ] using this

end MeasureTheory

