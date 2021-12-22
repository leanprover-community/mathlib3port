import Mathbin.Topology.UrysohnsLemma
import Mathbin.Topology.ContinuousFunction.Bounded

/-!
# Metrizability of a normal topological space with second countable topology

In this file we show that a normal topological space with second countable topology `X` is
metrizable: there exists a metric space structure that generates the same topology.

First we prove that `X` can be embedded into `l^∞`, then use this embedding to pull back the metric
space structure.
-/


open Set Filter Metric

open_locale BoundedContinuousFunction Filter TopologicalSpace

namespace TopologicalSpace

variable (X : Type _) [TopologicalSpace X] [NormalSpace X] [second_countable_topology X]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " A normal topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_embedding_l_infty [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `f)]
       [":"
        (Term.arrow
         `X
         "→"
         (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» (termℕ "ℕ") " →ᵇ " (Data.Real.Basic.termℝ "ℝ")))]))
     ","
     (Term.app `Embedding [`f]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rcases
         "rcases"
         [(Tactic.casesTarget [] (Term.app `exists_countable_basis [`X]))]
         ["with"
          (Tactic.rcasesPat.tuple
           "⟨"
           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `B)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hBc)]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
            ","
            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hB)]) [])]
           "⟩")])
        [])
       (group
        (Tactic.set
         "set"
         `s
         [":" (Term.app `Set [(«term_×_» (Term.app `Set [`X]) "×" (Term.app `Set [`X]))])]
         ":="
         (Set.«term{_|_}_1»
          "{"
          («term_∈_» `UV "∈" (Term.app `B.prod [`B]))
          "|"
          (Init.Core.«term_⊆_»
           (Term.app `Closure [(Term.proj `UV "." (fieldIdx "1"))])
           " ⊆ "
           (Term.proj `UV "." (fieldIdx "2")))
          "}")
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `Encodable [`s]))]
           ":="
           (Term.proj
            (Term.app
             (Term.proj (Term.app `hBc.prod [`hBc]) "." `mono)
             [(Term.app `inter_subset_left [(Term.hole "_") (Term.hole "_")])])
            "."
            `toEncodable))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `this'
           []
           [(Term.typeSpec ":" (Term.app `TopologicalSpace [`s]))]
           ":="
           (Order.BoundedOrder.«term⊥» "⊥"))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec ":" (Term.app `DiscreteTopology [`s]))]
           ":="
           (Term.anonymousCtor "⟨" [`rfl] "⟩"))))
        [])
       (group
        (Tactic.tacticSuffices_
         "suffices"
         (Term.sufficesDecl
          []
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `f)]
             [":"
              (Term.arrow
               `X
               "→"
               (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `s " →ᵇ " (Data.Real.Basic.termℝ "ℝ")))]))
           ","
           (Term.app `Embedding [`f]))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget [] `this)]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [])]
                    "=>"
                    (Term.app
                     (Term.proj (Term.app `f [`x]) "." `extend)
                     [(Term.app `Encodable.encode' [`s]) (numLit "0")])))
                  ","
                  (Term.app
                   (Term.proj
                    (Term.proj
                     (Term.app
                      `BoundedContinuousFunction.isometry_extend
                      [(Term.app `Encodable.encode' [`s])
                       (Term.paren
                        "("
                        [(numLit "0")
                         [(Term.typeAscription
                           ":"
                           (Topology.ContinuousFunction.Bounded.«term_→ᵇ_»
                            (termℕ "ℕ")
                            " →ᵇ "
                            (Data.Real.Basic.termℝ "ℝ")))]]
                        ")")])
                     "."
                     `Embedding)
                    "."
                    `comp)
                   [`hf])]
                 "⟩"))
               [])])))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hd []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`UV] [(Term.typeSpec ":" `s)])]
              ","
              (Term.app
               `Disjoint
               [(Term.app `Closure [(Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "1"))])
                (Order.BooleanAlgebra.«term_ᶜ»
                 (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "2"))
                 "ᶜ")])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`UV] [])]
             "=>"
             (Term.app
              `disjoint_compl_right.mono_right
              [(Term.app
                (Term.proj `compl_subset_compl "." (fieldIdx "2"))
                [(Term.proj (Term.proj `UV "." (fieldIdx "2")) "." (fieldIdx "2"))])]))))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε01)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hε)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            (Lean.unbracketedExplicitBinders
             [(Lean.binderIdent `ε)]
             [":" (Term.arrow `s "→" (Data.Real.Basic.termℝ "ℝ"))]))
           ","
           («term_∧_»
            (Term.forall
             "∀"
             [(Term.simpleBinder [`UV] [])]
             ","
             (Init.Core.«term_∈_»
              (Term.app `ε [`UV])
              " ∈ "
              (Term.app
               `Ioc
               [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                (numLit "1")])))
            "∧"
            (Term.app `tendsto [`ε `cofinite (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])])))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `posSumOfEncodable [`zero_lt_one `s]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hεc)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc1)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [`ε
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`UV] [])]
                  "=>"
                  (Term.anonymousCtor "⟨" [(Term.app `ε0 [`UV]) "," (Term.hole "_")] "⟩")))
                ","
                `hεc.summable.tendsto_cofinite_zero]
               "⟩"))
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj
                («term_$__»
                 (Term.app `le_has_sum [`hεc `UV])
                 "$"
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                   "=>"
                   (Term.proj (Term.app `ε0 [(Term.hole "_")]) "." `le))))
                "."
                `trans)
               [`hc1]))
             [])])))
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
              [(Term.simpleBinder [`UV] [(Term.typeSpec ":" `s)])]
              ","
              («term∃_,_»
               "∃"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `f)]
                 [":" (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")")]))
               ","
               («term_∧_»
                (Term.app `eq_on [`f (numLit "0") (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "1"))])
                "∧"
                («term_∧_»
                 (Term.app
                  `eq_on
                  [`f
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `ε [`UV])))
                   (Order.BooleanAlgebra.«term_ᶜ»
                    (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "2"))
                    "ᶜ")])
                 "∧"
                 (Term.forall
                  "∀"
                  [(Term.simpleBinder [`x] [])]
                  ","
                  (Init.Core.«term_∈_»
                   (Term.app `f [`x])
                   " ∈ "
                   (Term.app `Icc [(numLit "0") (Term.app `ε [`UV])]))))))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.intro "intro" [`UV]) [])
               (group
                (Tactic.rcases
                 "rcases"
                 [(Tactic.casesTarget
                   []
                   (Term.app
                    `exists_continuous_zero_one_of_closed
                    [`is_closed_closure
                     (Term.proj
                      (Term.app
                       `hB.is_open
                       [(Term.proj
                         (Term.proj (Term.proj `UV "." (fieldIdx "2")) "." (fieldIdx "1"))
                         "."
                         (fieldIdx "2"))])
                      "."
                      `is_closed_compl)
                     (Term.app `hd [`UV])]))]
                 ["with"
                  (Tactic.rcasesPat.tuple
                   "⟨"
                   [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf₀)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf₁)]) [])
                    ","
                    (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf01)]) [])]
                   "⟩")])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.anonymousCtor
                  "⟨"
                  [(Algebra.Group.Defs.«term_•_» (Term.app `ε [`UV]) " • " `f)
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x `hx] [])]
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simp
                           "simp"
                           []
                           []
                           ["[" [(Tactic.simpLemma [] [] (Term.app `hf₀ [(Term.app `subset_closure [`hx])]))] "]"]
                           [])
                          [])])))))
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x `hx] [])]
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `hf₁ [`hx]))] "]"] [])
                          [])])))))
                   ","
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`x] [])]
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.app
                        `mul_nonneg
                        [(Term.proj (Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "1")) "." `le)
                         (Term.proj (Term.app `hf01 [(Term.hole "_")]) "." (fieldIdx "1"))])
                       ","
                       (Term.app
                        `mul_le_of_le_one_right
                        [(Term.proj (Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "1")) "." `le)
                         (Term.proj (Term.app `hf01 [(Term.hole "_")]) "." (fieldIdx "2"))])]
                      "⟩")))]
                  "⟩"))
                [])]))))))
        [])
       (group (Tactic.choose "choose" [`f `hf0 `hfε `hf0ε] []) [])
       (group
        (Tactic.have''
         "have"
         [`hf01 []]
         [(Term.typeSpec
           ":"
           (Term.forall
            "∀"
            [(Term.simpleBinder [`UV `x] [])]
            ","
            (Init.Core.«term_∈_»
             (Term.app `f [`UV `x])
             " ∈ "
             (Term.app
              `Icc
              [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
               (numLit "1")]))))])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`UV `x] [])]
           "=>"
           (Term.app
            `Icc_subset_Icc_right
            [(Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "2"))
             (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])]))))
        [])
       (group
        (Tactic.set
         "set"
         `F
         [":"
          (Term.arrow `X "→" (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `s " →ᵇ " (Data.Real.Basic.termℝ "ℝ")))]
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder [`x] [])]
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.anonymousCtor
              "⟨"
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.app `f [`UV `x])))
               ","
               `continuous_of_discrete_topology]
              "⟩")
             ","
             (numLit "1")
             ","
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`UV₁ `UV₂] [])]
               "=>"
               (Term.app
                `Real.dist_le_of_mem_Icc_01
                [(Term.app `hf01 [(Term.hole "_") (Term.hole "_")])
                 (Term.app `hf01 [(Term.hole "_") (Term.hole "_")])])))]
            "⟩")))
         [])
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hF []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`x `UV] [])]
              ","
              («term_=_» (Term.app `F [`x `UV]) "=" (Term.app `f [`UV `x]))))]
           ":="
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`F
           ","
           (Term.app
            `Embedding.mk'
            [(Term.hole "_")
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `y `hxy] [])] "=>" (Term.hole "_")))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x] [])]
               "=>"
               (Term.app `le_antisymmₓ [(Term.hole "_") (Term.hole "_")])))])]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj `not_not "." (fieldIdx "1"))
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`Hne] [])] "=>" (Term.hole "_")))]))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.app (Term.proj `hB.mem_nhds_iff "." (fieldIdx "1")) [(Term.app `is_open_ne.mem_nhds [`Hne])]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `V)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVB)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxV)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVy)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hB.exists_closure_subset [(Term.app `hB.mem_nhds [`hVB `hxV])]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `U)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUB)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxU)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUV)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.set
              "set"
              `UV
              [":" (Init.Coe.«term↥_» "↥" `s)]
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Term.paren "(" [`U [(Term.tupleTail "," [`V])]] ")")
                ","
                (Term.anonymousCtor "⟨" [`hUB "," `hVB] "⟩")
                ","
                `hUV]
               "⟩")
              [])
             [])
            (group (Tactic.apply "apply" (Term.proj (Term.proj (Term.app `ε01 [`UV]) "." (fieldIdx "1")) "." `Ne)) [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_=_»
                 (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                 "="
                 (Term.app `F [`x `UV]))
                ":="
                (Term.proj (Term.app `hf0 [`UV `hxU]) "." `symm))
               (calcStep
                («term_=_» (Term.hole "_") "=" (Term.app `F [`y `UV]))
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy)] "]") []) [])]))))
               (calcStep
                («term_=_» (Term.hole "_") "=" (Term.app `ε [`UV]))
                ":="
                (Term.app
                 `hfε
                 [`UV
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`h] [(Term.typeSpec ":" (Init.Core.«term_∈_» `y " ∈ " `V))])]
                    "=>"
                    (Term.app `hVy [`h `rfl])))]))])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.app
                 (Term.proj (Term.app `nhds_basis_ball.comap [(Term.hole "_")]) "." `le_basis_iff)
                 [`hB.nhds_has_basis])
                "."
                (fieldIdx "2"))
               [(Term.hole "_")]))
             [])
            (group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one (Tactic.rcasesPat.one `V))
               (Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVB)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxV)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `hB.exists_closure_subset [(Term.app `hB.mem_nhds [`hVB `hxV])]))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `U)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUB)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxU)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUV)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.set
              "set"
              `UV
              [":" (Init.Coe.«term↥_» "↥" `s)]
              ":="
              (Term.anonymousCtor
               "⟨"
               [(Term.paren "(" [`U [(Term.tupleTail "," [`V])]] ")")
                ","
                (Term.anonymousCtor "⟨" [`hUB "," `hVB] "⟩")
                ","
                `hUV]
               "⟩")
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `ε [`UV])
                ","
                (Term.proj (Term.app `ε01 [`UV]) "." (fieldIdx "1"))
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`y] [])
                   (Term.simpleBinder
                    [`hy]
                    [(Term.typeSpec
                      ":"
                      («term_<_» (Term.app `dist [(Term.app `F [`y]) (Term.app `F [`x])]) "<" (Term.app `ε [`UV])))])]
                  "=>"
                  (Term.hole "_")))]
               "⟩"))
             [])
            (group
             (Tactic.replace'
              "replace"
              [`hy []]
              [(Term.typeSpec
                ":"
                («term_<_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "<" (Term.app `ε [`UV])))])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app
               (Term.proj (Term.app `BoundedContinuousFunction.dist_coe_le_dist [(Term.hole "_")]) "." `trans_lt)
               [`hy]))
             [])
            (group (Tactic.contrapose! "contrapose!" [`hy []]) [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `hF)
                ","
                (Tactic.rwRule [] `hF)
                ","
                (Tactic.rwRule [] (Term.app `hfε [`UV `hy]))
                ","
                (Tactic.rwRule [] (Term.app `hf0 [`UV `hxU]))
                ","
                (Tactic.rwRule [] `Pi.zero_apply)
                ","
                (Tactic.rwRule [] `dist_zero_right)]
               "]")
              [])
             [])
            (group (Tactic.exact "exact" (Term.app `le_abs_self [(Term.hole "_")])) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.proj (Term.app `nhds_basis_closed_ball.comap [(Term.hole "_")]) "." `ge_iff)
                "."
                (fieldIdx "2"))
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`δ `δ0] [])] "=>" (Term.hole "_")))]))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`h_fin []]
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `finite
                   [(Set.«term{_|_}»
                     "{"
                     (Mathlib.ExtendedBinder.extBinder `UV [":" `s])
                     "|"
                     («term_≤_» `δ "≤" (Term.app `ε [`UV]))
                     "}")]))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.simpa
                      "simpa"
                      []
                      ["only"]
                      ["[" [(Tactic.simpLemma [] ["←"] `not_ltₓ)] "]"]
                      []
                      ["using" (Term.app `hε [(Term.app `gt_mem_nhds [`δ0])])])
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                []
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
                   " in "
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
                   ", "
                   (Term.forall
                    "∀"
                    [(Term.simpleBinder [`UV] [])]
                    ","
                    (Term.arrow
                     («term_≤_» `δ "≤" (Term.app `ε [`UV]))
                     "→"
                     («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
                       [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
                       [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
                     [])]))))))
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               `this.mono
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`y `hy] [])]
                  "=>"
                  («term_$__»
                   (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
                   "$"
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))]))
             [])
            (group
             (Tactic.cases'
              "cases'"
              [(Tactic.casesTarget [] (Term.app `le_totalₓ [`δ (Term.app `ε [`UV])]))]
              []
              ["with" [(Lean.binderIdent `hle) (Lean.binderIdent `hle)]])
             [])
            (group
             (exacts
              "exacts"
              "["
              [(Term.app `hy [(Term.hole "_") `hle])
               ","
               (Term.app
                (Term.proj
                 (Term.app
                  `Real.dist_le_of_mem_Icc
                  [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])
                   (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
                 "."
                 `trans)
                [(Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))])]
              "]")
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
       (Tactic.rcases
        "rcases"
        [(Tactic.casesTarget [] (Term.app `exists_countable_basis [`X]))]
        ["with"
         (Tactic.rcasesPat.tuple
          "⟨"
          [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `B)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hBc)]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.clear "-")]) [])
           ","
           (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hB)]) [])]
          "⟩")])
       [])
      (group
       (Tactic.set
        "set"
        `s
        [":" (Term.app `Set [(«term_×_» (Term.app `Set [`X]) "×" (Term.app `Set [`X]))])]
        ":="
        (Set.«term{_|_}_1»
         "{"
         («term_∈_» `UV "∈" (Term.app `B.prod [`B]))
         "|"
         (Init.Core.«term_⊆_»
          (Term.app `Closure [(Term.proj `UV "." (fieldIdx "1"))])
          " ⊆ "
          (Term.proj `UV "." (fieldIdx "2")))
         "}")
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `Encodable [`s]))]
          ":="
          (Term.proj
           (Term.app
            (Term.proj (Term.app `hBc.prod [`hBc]) "." `mono)
            [(Term.app `inter_subset_left [(Term.hole "_") (Term.hole "_")])])
           "."
           `toEncodable))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `this'
          []
          [(Term.typeSpec ":" (Term.app `TopologicalSpace [`s]))]
          ":="
          (Order.BoundedOrder.«term⊥» "⊥"))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec ":" (Term.app `DiscreteTopology [`s]))]
          ":="
          (Term.anonymousCtor "⟨" [`rfl] "⟩"))))
       [])
      (group
       (Tactic.tacticSuffices_
        "suffices"
        (Term.sufficesDecl
         []
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `f)]
            [":"
             (Term.arrow
              `X
              "→"
              (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `s " →ᵇ " (Data.Real.Basic.termℝ "ℝ")))]))
          ","
          (Term.app `Embedding [`f]))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] `this)]
               ["with"
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf)]) [])]
                 "⟩")])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`x] [])]
                   "=>"
                   (Term.app
                    (Term.proj (Term.app `f [`x]) "." `extend)
                    [(Term.app `Encodable.encode' [`s]) (numLit "0")])))
                 ","
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.app
                     `BoundedContinuousFunction.isometry_extend
                     [(Term.app `Encodable.encode' [`s])
                      (Term.paren
                       "("
                       [(numLit "0")
                        [(Term.typeAscription
                          ":"
                          (Topology.ContinuousFunction.Bounded.«term_→ᵇ_»
                           (termℕ "ℕ")
                           " →ᵇ "
                           (Data.Real.Basic.termℝ "ℝ")))]]
                       ")")])
                    "."
                    `Embedding)
                   "."
                   `comp)
                  [`hf])]
                "⟩"))
              [])])))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hd []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`UV] [(Term.typeSpec ":" `s)])]
             ","
             (Term.app
              `Disjoint
              [(Term.app `Closure [(Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "1"))])
               (Order.BooleanAlgebra.«term_ᶜ»
                (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "2"))
                "ᶜ")])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`UV] [])]
            "=>"
            (Term.app
             `disjoint_compl_right.mono_right
             [(Term.app
               (Term.proj `compl_subset_compl "." (fieldIdx "2"))
               [(Term.proj (Term.proj `UV "." (fieldIdx "2")) "." (fieldIdx "2"))])]))))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε01)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hε)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `ε)]
            [":" (Term.arrow `s "→" (Data.Real.Basic.termℝ "ℝ"))]))
          ","
          («term_∧_»
           (Term.forall
            "∀"
            [(Term.simpleBinder [`UV] [])]
            ","
            (Init.Core.«term_∈_»
             (Term.app `ε [`UV])
             " ∈ "
             (Term.app
              `Ioc
              [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
               (numLit "1")])))
           "∧"
           (Term.app `tendsto [`ε `cofinite (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])])))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `posSumOfEncodable [`zero_lt_one `s]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ε0)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hεc)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hc1)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [`ε
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`UV] [])]
                 "=>"
                 (Term.anonymousCtor "⟨" [(Term.app `ε0 [`UV]) "," (Term.hole "_")] "⟩")))
               ","
               `hεc.summable.tendsto_cofinite_zero]
              "⟩"))
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj
               («term_$__»
                (Term.app `le_has_sum [`hεc `UV])
                "$"
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])]
                  "=>"
                  (Term.proj (Term.app `ε0 [(Term.hole "_")]) "." `le))))
               "."
               `trans)
              [`hc1]))
            [])])))
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
             [(Term.simpleBinder [`UV] [(Term.typeSpec ":" `s)])]
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `f)]
                [":" (Topology.ContinuousFunction.Basic.«termC(_,_)» "C(" `X ", " (Data.Real.Basic.termℝ "ℝ") ")")]))
              ","
              («term_∧_»
               (Term.app `eq_on [`f (numLit "0") (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "1"))])
               "∧"
               («term_∧_»
                (Term.app
                 `eq_on
                 [`f
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" (Term.app `ε [`UV])))
                  (Order.BooleanAlgebra.«term_ᶜ»
                   (Term.proj (Term.proj `UV "." (fieldIdx "1")) "." (fieldIdx "2"))
                   "ᶜ")])
                "∧"
                (Term.forall
                 "∀"
                 [(Term.simpleBinder [`x] [])]
                 ","
                 (Init.Core.«term_∈_»
                  (Term.app `f [`x])
                  " ∈ "
                  (Term.app `Icc [(numLit "0") (Term.app `ε [`UV])]))))))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.intro "intro" [`UV]) [])
              (group
               (Tactic.rcases
                "rcases"
                [(Tactic.casesTarget
                  []
                  (Term.app
                   `exists_continuous_zero_one_of_closed
                   [`is_closed_closure
                    (Term.proj
                     (Term.app
                      `hB.is_open
                      [(Term.proj
                        (Term.proj (Term.proj `UV "." (fieldIdx "2")) "." (fieldIdx "1"))
                        "."
                        (fieldIdx "2"))])
                     "."
                     `is_closed_compl)
                    (Term.app `hd [`UV])]))]
                ["with"
                 (Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf₀)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf₁)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hf01)]) [])]
                  "⟩")])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.anonymousCtor
                 "⟨"
                 [(Algebra.Group.Defs.«term_•_» (Term.app `ε [`UV]) " • " `f)
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x `hx] [])]
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simp
                          "simp"
                          []
                          []
                          ["[" [(Tactic.simpLemma [] [] (Term.app `hf₀ [(Term.app `subset_closure [`hx])]))] "]"]
                          [])
                         [])])))))
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x `hx] [])]
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] (Term.app `hf₁ [`hx]))] "]"] [])
                         [])])))))
                  ","
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`x] [])]
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.app
                       `mul_nonneg
                       [(Term.proj (Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "1")) "." `le)
                        (Term.proj (Term.app `hf01 [(Term.hole "_")]) "." (fieldIdx "1"))])
                      ","
                      (Term.app
                       `mul_le_of_le_one_right
                       [(Term.proj (Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "1")) "." `le)
                        (Term.proj (Term.app `hf01 [(Term.hole "_")]) "." (fieldIdx "2"))])]
                     "⟩")))]
                 "⟩"))
               [])]))))))
       [])
      (group (Tactic.choose "choose" [`f `hf0 `hfε `hf0ε] []) [])
      (group
       (Tactic.have''
        "have"
        [`hf01 []]
        [(Term.typeSpec
          ":"
          (Term.forall
           "∀"
           [(Term.simpleBinder [`UV `x] [])]
           ","
           (Init.Core.«term_∈_»
            (Term.app `f [`UV `x])
            " ∈ "
            (Term.app
             `Icc
             [(Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
              (numLit "1")]))))])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`UV `x] [])]
          "=>"
          (Term.app
           `Icc_subset_Icc_right
           [(Term.proj (Term.app `ε01 [(Term.hole "_")]) "." (fieldIdx "2"))
            (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])]))))
       [])
      (group
       (Tactic.set
        "set"
        `F
        [":" (Term.arrow `X "→" (Topology.ContinuousFunction.Bounded.«term_→ᵇ_» `s " →ᵇ " (Data.Real.Basic.termℝ "ℝ")))]
        ":="
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`x] [])]
          "=>"
          (Term.anonymousCtor
           "⟨"
           [(Term.anonymousCtor
             "⟨"
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.app `f [`UV `x])))
              ","
              `continuous_of_discrete_topology]
             "⟩")
            ","
            (numLit "1")
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`UV₁ `UV₂] [])]
              "=>"
              (Term.app
               `Real.dist_le_of_mem_Icc_01
               [(Term.app `hf01 [(Term.hole "_") (Term.hole "_")])
                (Term.app `hf01 [(Term.hole "_") (Term.hole "_")])])))]
           "⟩")))
        [])
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hF []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`x `UV] [])]
             ","
             («term_=_» (Term.app `F [`x `UV]) "=" (Term.app `f [`UV `x]))))]
          ":="
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`F
          ","
          (Term.app
           `Embedding.mk'
           [(Term.hole "_")
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`x `y `hxy] [])] "=>" (Term.hole "_")))
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`x] [])]
              "=>"
              (Term.app `le_antisymmₓ [(Term.hole "_") (Term.hole "_")])))])]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj `not_not "." (fieldIdx "1"))
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`Hne] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.app (Term.proj `hB.mem_nhds_iff "." (fieldIdx "1")) [(Term.app `is_open_ne.mem_nhds [`Hne])]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `V)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVB)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxV)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVy)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hB.exists_closure_subset [(Term.app `hB.mem_nhds [`hVB `hxV])]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `U)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUB)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxU)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUV)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.set
             "set"
             `UV
             [":" (Init.Coe.«term↥_» "↥" `s)]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Term.paren "(" [`U [(Term.tupleTail "," [`V])]] ")")
               ","
               (Term.anonymousCtor "⟨" [`hUB "," `hVB] "⟩")
               ","
               `hUV]
              "⟩")
             [])
            [])
           (group (Tactic.apply "apply" (Term.proj (Term.proj (Term.app `ε01 [`UV]) "." (fieldIdx "1")) "." `Ne)) [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_=_»
                (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                "="
                (Term.app `F [`x `UV]))
               ":="
               (Term.proj (Term.app `hf0 [`UV `hxU]) "." `symm))
              (calcStep
               («term_=_» (Term.hole "_") "=" (Term.app `F [`y `UV]))
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hxy)] "]") []) [])]))))
              (calcStep
               («term_=_» (Term.hole "_") "=" (Term.app `ε [`UV]))
               ":="
               (Term.app
                `hfε
                [`UV
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`h] [(Term.typeSpec ":" (Init.Core.«term_∈_» `y " ∈ " `V))])]
                   "=>"
                   (Term.app `hVy [`h `rfl])))]))])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.app
                (Term.proj (Term.app `nhds_basis_ball.comap [(Term.hole "_")]) "." `le_basis_iff)
                [`hB.nhds_has_basis])
               "."
               (fieldIdx "2"))
              [(Term.hole "_")]))
            [])
           (group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.one `V))
              (Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hVB)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxV)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget [] (Term.app `hB.exists_closure_subset [(Term.app `hB.mem_nhds [`hVB `hxV])]))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `U)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUB)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hxU)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hUV)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.set
             "set"
             `UV
             [":" (Init.Coe.«term↥_» "↥" `s)]
             ":="
             (Term.anonymousCtor
              "⟨"
              [(Term.paren "(" [`U [(Term.tupleTail "," [`V])]] ")")
               ","
               (Term.anonymousCtor "⟨" [`hUB "," `hVB] "⟩")
               ","
               `hUV]
              "⟩")
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `ε [`UV])
               ","
               (Term.proj (Term.app `ε01 [`UV]) "." (fieldIdx "1"))
               ","
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`y] [])
                  (Term.simpleBinder
                   [`hy]
                   [(Term.typeSpec
                     ":"
                     («term_<_» (Term.app `dist [(Term.app `F [`y]) (Term.app `F [`x])]) "<" (Term.app `ε [`UV])))])]
                 "=>"
                 (Term.hole "_")))]
              "⟩"))
            [])
           (group
            (Tactic.replace'
             "replace"
             [`hy []]
             [(Term.typeSpec
               ":"
               («term_<_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "<" (Term.app `ε [`UV])))])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              (Term.proj (Term.app `BoundedContinuousFunction.dist_coe_le_dist [(Term.hole "_")]) "." `trans_lt)
              [`hy]))
            [])
           (group (Tactic.contrapose! "contrapose!" [`hy []]) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `hF)
               ","
               (Tactic.rwRule [] `hF)
               ","
               (Tactic.rwRule [] (Term.app `hfε [`UV `hy]))
               ","
               (Tactic.rwRule [] (Term.app `hf0 [`UV `hxU]))
               ","
               (Tactic.rwRule [] `Pi.zero_apply)
               ","
               (Tactic.rwRule [] `dist_zero_right)]
              "]")
             [])
            [])
           (group (Tactic.exact "exact" (Term.app `le_abs_self [(Term.hole "_")])) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.proj (Term.app `nhds_basis_closed_ball.comap [(Term.hole "_")]) "." `ge_iff)
               "."
               (fieldIdx "2"))
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`δ `δ0] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`h_fin []]
               [(Term.typeSpec
                 ":"
                 (Term.app
                  `finite
                  [(Set.«term{_|_}»
                    "{"
                    (Mathlib.ExtendedBinder.extBinder `UV [":" `s])
                    "|"
                    («term_≤_» `δ "≤" (Term.app `ε [`UV]))
                    "}")]))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.simpa
                     "simpa"
                     []
                     ["only"]
                     ["[" [(Tactic.simpLemma [] ["←"] `not_ltₓ)] "]"]
                     []
                     ["using" (Term.app `hε [(Term.app `gt_mem_nhds [`δ0])])])
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               []
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
                  " in "
                  (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
                  ", "
                  (Term.forall
                   "∀"
                   [(Term.simpleBinder [`UV] [])]
                   ","
                   (Term.arrow
                    («term_≤_» `δ "≤" (Term.app `ε [`UV]))
                    "→"
                    («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
                      [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
                      [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
                    [])]))))))
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              `this.mono
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`y `hy] [])]
                 "=>"
                 («term_$__»
                  (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
                  "$"
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))]))
            [])
           (group
            (Tactic.cases'
             "cases'"
             [(Tactic.casesTarget [] (Term.app `le_totalₓ [`δ (Term.app `ε [`UV])]))]
             []
             ["with" [(Lean.binderIdent `hle) (Lean.binderIdent `hle)]])
            [])
           (group
            (exacts
             "exacts"
             "["
             [(Term.app `hy [(Term.hole "_") `hle])
              ","
              (Term.app
               (Term.proj
                (Term.app
                 `Real.dist_le_of_mem_Icc
                 [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])
                  (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
                "."
                `trans)
               [(Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))])]
             "]")
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
     [(group
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj
          (Term.proj (Term.app `nhds_basis_closed_ball.comap [(Term.hole "_")]) "." `ge_iff)
          "."
          (fieldIdx "2"))
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`δ `δ0] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_fin []]
          [(Term.typeSpec
            ":"
            (Term.app
             `finite
             [(Set.«term{_|_}»
               "{"
               (Mathlib.ExtendedBinder.extBinder `UV [":" `s])
               "|"
               («term_≤_» `δ "≤" (Term.app `ε [`UV]))
               "}")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.simpa
                "simpa"
                []
                ["only"]
                ["[" [(Tactic.simpLemma [] ["←"] `not_ltₓ)] "]"]
                []
                ["using" (Term.app `hε [(Term.app `gt_mem_nhds [`δ0])])])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
             "∀ᶠ"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
             " in "
             (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
             ", "
             (Term.forall
              "∀"
              [(Term.simpleBinder [`UV] [])]
              ","
              (Term.arrow
               («term_≤_» `δ "≤" (Term.app `ε [`UV]))
               "→"
               («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
                 [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `this.mono
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`y `hy] [])]
            "=>"
            («term_$__»
             (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
             "$"
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))]))
       [])
      (group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `le_totalₓ [`δ (Term.app `ε [`UV])]))]
        []
        ["with" [(Lean.binderIdent `hle) (Lean.binderIdent `hle)]])
       [])
      (group
       (exacts
        "exacts"
        "["
        [(Term.app `hy [(Term.hole "_") `hle])
         ","
         (Term.app
          (Term.proj
           (Term.app
            `Real.dist_le_of_mem_Icc
            [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
           "."
           `trans)
          [(Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))])]
        "]")
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (exacts
   "exacts"
   "["
   [(Term.app `hy [(Term.hole "_") `hle])
    ","
    (Term.app
     (Term.proj
      (Term.app
       `Real.dist_le_of_mem_Icc
       [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
      "."
      `trans)
     [(Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))])]
   "]")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'exacts', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `Real.dist_le_of_mem_Icc
     [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
    "."
    `trans)
   [(Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sub_zero)] "]") []) [])])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    `Real.dist_le_of_mem_Icc
    [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
   "."
   `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `Real.dist_le_of_mem_Icc
   [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])
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
  `hf0ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hf0ε [(Term.hole "_") (Term.hole "_")])
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
  `hf0ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Real.dist_le_of_mem_Icc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `Real.dist_le_of_mem_Icc
   [(Term.paren "(" [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) []] ")")
    (Term.paren "(" [(Term.app `hf0ε [(Term.hole "_") (Term.hole "_")]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hy [(Term.hole "_") `hle])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hle
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hy
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.cases'
   "cases'"
   [(Tactic.casesTarget [] (Term.app `le_totalₓ [`δ (Term.app `ε [`UV])]))]
   []
   ["with" [(Lean.binderIdent `hle) (Lean.binderIdent `hle)]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases'', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.binderIdent', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `le_totalₓ [`δ (Term.app `ε [`UV])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ε [`UV])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `UV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `ε [`UV]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `le_totalₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `this.mono
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`y `hy] [])]
       "=>"
       («term_$__»
        (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
        "$"
        (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `this.mono
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`y `hy] [])]
      "=>"
      («term_$__»
       (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
       "$"
       (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))])
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
    [(Term.simpleBinder [`y `hy] [])]
    "=>"
    («term_$__»
     (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
     "$"
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_$__»
   (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
   "$"
   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_$__»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
  (Term.proj (Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `BoundedContinuousFunction.dist_le [`δ0.le])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ0.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `BoundedContinuousFunction.dist_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `BoundedContinuousFunction.dist_le [`δ0.le]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `this.mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
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
       (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
        "∀ᶠ"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
        " in "
        (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
        ", "
        (Term.forall
         "∀"
         [(Term.simpleBinder [`UV] [])]
         ","
         (Term.arrow
          («term_≤_» `δ "≤" (Term.app `ε [`UV]))
          "→"
          («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)))))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
            [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
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
       (Tactic.refine'
        "refine'"
        (Term.app
         (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
         [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
         [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
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
    (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
    [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
   [`x (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ0
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `closed_ball_mem_nhds
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `closed_ball_mem_nhds [(Term.hole "_") `δ0]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.proj (Term.app `f [`UV]) "." `Continuous) "." `Tendsto)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `f [`UV]) "." `Continuous)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `f [`UV])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `UV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `f [`UV]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
    [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
   [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`UV `hUV] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `eventually_all_finite [`h_fin]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `eventually_all_finite [`h_fin])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_fin
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `eventually_all_finite
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `eventually_all_finite [`h_fin]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
   "∀ᶠ"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `y)] []))
   " in "
   (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
   ", "
   (Term.forall
    "∀"
    [(Term.simpleBinder [`UV] [])]
    ","
    (Term.arrow
     («term_≤_» `δ "≤" (Term.app `ε [`UV]))
     "→"
     («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`UV] [])]
   ","
   (Term.arrow
    («term_≤_» `δ "≤" (Term.app `ε [`UV]))
    "→"
    («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.arrow
   («term_≤_» `δ "≤" (Term.app `ε [`UV]))
   "→"
   («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.arrow', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])]) "≤" `δ)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `dist [(Term.app `F [`y `UV]) (Term.app `F [`x `UV])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `F [`x `UV])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `UV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `F [`x `UV]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `F [`y `UV])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `UV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `y
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `F
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `F [`y `UV]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dist
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 25 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 25, term))
  («term_≤_» `δ "≤" (Term.app `ε [`UV]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ε [`UV])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `UV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ε
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `δ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 25, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 25, (some 25, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Topology.Basic.term𝓝 "𝓝") [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Topology.Basic.term𝓝 "𝓝")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Topology.Basic.term𝓝', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/--
    A normal topological space with second countable topology can be embedded into `l^∞ = ℕ →ᵇ ℝ`.
    -/
  theorem
    exists_embedding_l_infty
    : ∃ f : X → ℕ →ᵇ ℝ , Embedding f
    :=
      by
        rcases exists_countable_basis X with ⟨ B , hBc , - , hB ⟩
          set s : Set Set X × Set X := { UV ∈ B.prod B | Closure UV . 1 ⊆ UV . 2 }
          have : Encodable s := hBc.prod hBc . mono inter_subset_left _ _ . toEncodable
          let this' : TopologicalSpace s := ⊥
          have : DiscreteTopology s := ⟨ rfl ⟩
          suffices
            ∃ f : X → s →ᵇ ℝ , Embedding f
              by
                rcases this with ⟨ f , hf ⟩
                  exact
                    ⟨
                      fun x => f x . extend Encodable.encode' s 0
                        ,
                        BoundedContinuousFunction.isometry_extend Encodable.encode' s ( 0 : ℕ →ᵇ ℝ ) . Embedding . comp
                          hf
                      ⟩
          have
            hd
              : ∀ UV : s , Disjoint Closure UV . 1 . 1 UV . 1 . 2 ᶜ
              :=
              fun UV => disjoint_compl_right.mono_right compl_subset_compl . 2 UV . 2 . 2
          obtain ⟨ ε , ε01 , hε ⟩ : ∃ ε : s → ℝ , ∀ UV , ε UV ∈ Ioc ( 0 : ℝ ) 1 ∧ tendsto ε cofinite 𝓝 0
          ·
            rcases posSumOfEncodable zero_lt_one s with ⟨ ε , ε0 , c , hεc , hc1 ⟩
              refine' ⟨ ε , fun UV => ⟨ ε0 UV , _ ⟩ , hεc.summable.tendsto_cofinite_zero ⟩
              exact le_has_sum hεc UV $ fun _ _ => ε0 _ . le . trans hc1
          have
            :
                ∀
                  UV : s
                  ,
                  ∃ f : C( X , ℝ ) , eq_on f 0 UV . 1 . 1 ∧ eq_on f fun _ => ε UV UV . 1 . 2 ᶜ ∧ ∀ x , f x ∈ Icc 0 ε UV
              :=
              by
                intro UV
                  rcases
                    exists_continuous_zero_one_of_closed
                      is_closed_closure hB.is_open UV . 2 . 1 . 2 . is_closed_compl hd UV
                    with ⟨ f , hf₀ , hf₁ , hf01 ⟩
                  exact
                    ⟨
                      ε UV • f
                        ,
                        fun x hx => by simp [ hf₀ subset_closure hx ]
                        ,
                        fun x hx => by simp [ hf₁ hx ]
                        ,
                        fun
                          x
                            =>
                            ⟨ mul_nonneg ε01 _ . 1 . le hf01 _ . 1 , mul_le_of_le_one_right ε01 _ . 1 . le hf01 _ . 2 ⟩
                      ⟩
          choose f hf0 hfε hf0ε
          have hf01 : ∀ UV x , f UV x ∈ Icc ( 0 : ℝ ) 1
          exact fun UV x => Icc_subset_Icc_right ε01 _ . 2 hf0ε _ _
          set
            F
            : X → s →ᵇ ℝ
            :=
            fun
              x
                =>
                ⟨
                  ⟨ fun UV => f UV x , continuous_of_discrete_topology ⟩
                    ,
                    1
                    ,
                    fun UV₁ UV₂ => Real.dist_le_of_mem_Icc_01 hf01 _ _ hf01 _ _
                  ⟩
          have hF : ∀ x UV , F x UV = f UV x := fun _ _ => rfl
          refine' ⟨ F , Embedding.mk' _ fun x y hxy => _ fun x => le_antisymmₓ _ _ ⟩
          ·
            refine' not_not . 1 fun Hne => _
              rcases hB.mem_nhds_iff . 1 is_open_ne.mem_nhds Hne with ⟨ V , hVB , hxV , hVy ⟩
              rcases hB.exists_closure_subset hB.mem_nhds hVB hxV with ⟨ U , hUB , hxU , hUV ⟩
              set UV : ↥ s := ⟨ ( U , V ) , ⟨ hUB , hVB ⟩ , hUV ⟩
              apply ε01 UV . 1 . Ne
              calc
                ( 0 : ℝ ) = F x UV := hf0 UV hxU . symm
                  _ = F y UV := by rw [ hxy ]
                  _ = ε UV := hfε UV fun h : y ∈ V => hVy h rfl
          ·
            refine' nhds_basis_ball.comap _ . le_basis_iff hB.nhds_has_basis . 2 _
              rintro V ⟨ hVB , hxV ⟩
              rcases hB.exists_closure_subset hB.mem_nhds hVB hxV with ⟨ U , hUB , hxU , hUV ⟩
              set UV : ↥ s := ⟨ ( U , V ) , ⟨ hUB , hVB ⟩ , hUV ⟩
              refine' ⟨ ε UV , ε01 UV . 1 , fun y hy : dist F y F x < ε UV => _ ⟩
              replace hy : dist F y UV F x UV < ε UV
              exact BoundedContinuousFunction.dist_coe_le_dist _ . trans_lt hy
              contrapose! hy
              rw [ hF , hF , hfε UV hy , hf0 UV hxU , Pi.zero_apply , dist_zero_right ]
              exact le_abs_self _
          ·
            refine' nhds_basis_closed_ball.comap _ . ge_iff . 2 fun δ δ0 => _
              have h_fin : finite { UV : s | δ ≤ ε UV } := by simpa only [ ← not_ltₓ ] using hε gt_mem_nhds δ0
              have
                : ∀ᶠ y in 𝓝 x , ∀ UV , δ ≤ ε UV → dist F y UV F x UV ≤ δ
                  :=
                  by
                    refine' eventually_all_finite h_fin . 2 fun UV hUV => _
                      exact f UV . Continuous . Tendsto x closed_ball_mem_nhds _ δ0
              refine' this.mono fun y hy => BoundedContinuousFunction.dist_le δ0.le . 2 $ fun UV => _
              cases' le_totalₓ δ ε UV with hle hle
              exacts [ hy _ hle , Real.dist_le_of_mem_Icc hf0ε _ _ hf0ε _ _ . trans by rwa [ sub_zero ] ]

/--  A normal topological space with second countable topology `X` is metrizable: there exists a
metric space structure that generates the same topology. This definition provides a `metric_space`
instance such that the corresponding `topological_space X` instance is definitionally equal
to the original one. -/
@[reducible]
noncomputable def to_metric_space : MetricSpace X :=
  @MetricSpace.replaceUniformity X
    ((UniformSpace.comap (exists_embedding_l_infty X).some inferInstance).replaceTopology
      (exists_embedding_l_infty X).some_spec.induced)
    (MetricSpace.induced (exists_embedding_l_infty X).some (exists_embedding_l_infty X).some_spec.inj inferInstance) rfl

end TopologicalSpace

