import Mathbin.Topology.Category.Profinite.Default
import Mathbin.Topology.LocallyConstant.Basic
import Mathbin.Topology.DiscreteQuotient

/-!
# Cofiltered limits of profinite sets.

This file contains some theorems about cofiltered limits of profinite sets.

## Main Results

- `exists_clopen_of_cofiltered` shows that any clopen set in a cofiltered limit of profinite
  sets is the pullback of a clopen set from one of the factors in the limit.
- `exists_locally_constant` shows that any locally constant function from a cofiltered limit
  of profinite sets factors through one of the components.
-/


namespace Profinite

open_locale Classical

open CategoryTheory

open CategoryTheory.Limits

universe u

variable {J : Type u} [small_category J] [is_cofiltered J] {F : J ⥤ Profinite.{u}} (C : cone F) (hC : is_limit C)

include hC

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIf `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from\na clopen set in one of the terms in the limit.\n-/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `exists_clopen_of_cofiltered [])
  (Command.declSig
   [(Term.implicitBinder "{" [`U] [":" (Term.app `Set [`C.X])] "}")
    (Term.explicitBinder "(" [`hU] [":" (Term.app `IsClopen [`U])] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `j)] ":" `J ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `V)] ":" (Term.app `Set [(Term.app `F.obj [`j])]) ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hV)] ":" (Term.app `IsClopen [`V]) ")")])
     ","
     («term_=_» `U "=" (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `C.π.app [`j]) " ⁻¹' " `V)))))
  (Command.declValSimple
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
           [`hB []]
           []
           ":="
           (Term.app
            `Top.is_topological_basis_cofiltered_limit
            [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `Profinite.toTop)
             (Term.app `Profinite.to_Top.map_cone [`C])
             (Term.app `is_limit_of_preserves [(Term.hole "_") `hC])
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`j] [])]
               "=>"
               (Set.«term{_|_}» "{" `W "|" (Term.app `IsClopen [`W]) "}")))
             (Term.hole "_")
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `is_clopen_univ))
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`i `U1 `U2 `hU1 `hU2] [])] "=>" (Term.app `hU1.inter [`hU2])))
             (Term.hole "_")]))))
        [])
       (group (Tactic.rotate "rotate" []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`i]) [])
            (group
             (Tactic.change
              "change"
              (Term.app
               `TopologicalSpace.IsTopologicalBasis
               [(Set.«term{_|_}»
                 "{"
                 (Mathlib.ExtendedBinder.extBinder `W [":" (Term.app `Set [(Term.app `F.obj [`i])])])
                 "|"
                 (Term.app `IsClopen [`W])
                 "}")])
              [])
             [])
            (group (Tactic.apply "apply" `is_topological_basis_clopen) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one (Tactic.rcasesPat.one `i))
               (Tactic.rintroPat.one (Tactic.rcasesPat.one `j))
               (Tactic.rintroPat.one (Tactic.rcasesPat.one `f))
               (Tactic.rintroPat.one (Tactic.rcasesPat.one `V))
               (Tactic.rintroPat.one
                (Tactic.rcasesPat.paren
                 "("
                 (Tactic.rcasesPatLo
                  (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hV)])
                  [":" (Term.app `IsClopen [(Term.hole "_")])])
                 ")"))]
              [])
             [])
            (group
             (Tactic.«tactic_<;>_»
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.app (Term.proj (Term.proj `hV "." (fieldIdx "1")) "." `Preimage) [(Term.hole "_")])
                 ","
                 (Term.app (Term.proj (Term.proj `hV "." (fieldIdx "2")) "." `Preimage) [(Term.hole "_")])]
                "⟩"))
              "<;>"
              (Tactic.continuity "continuity" []))
             [])])))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `hB.open_eq_sUnion [(Term.proj `hU "." (fieldIdx "1"))])]])
        [])
       (group (Tactic.clear "clear" [`hB]) [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `j
           [(Term.typeSpec ":" (Term.arrow `S "→" `J))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `V
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
              ","
              (Term.app `Set [(Term.app `F.obj [(Term.app `j [`s])])])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             (Term.proj (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some_spec) "." `some))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hV []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
              ","
              («term_∧_»
               (Term.app `IsClopen [(Term.app `V [`s])])
               "∧"
               («term_=_»
                (Term.proj `s "." (fieldIdx "1"))
                "="
                (Set.Data.Set.Basic.«term_⁻¹'_»
                 (Term.app `C.π.app [(Term.app `j [`s])])
                 " ⁻¹' "
                 (Term.app `V [`s]))))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             (Term.proj
              (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some_spec)
              "."
              `some_spec))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           []
           ":="
           (Term.app
            (Term.proj (Term.proj (Term.proj `hU "." (fieldIdx "2")) "." `IsCompact) "." `elim_finite_subcover)
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
               "=>"
               (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `C.π.app [(Term.app `j [`s])]) " ⁻¹' " (Term.app `V [`s]))))
             (Term.hole "_")
             (Term.hole "_")]))))
        [])
       (group (Tactic.rotate "rotate" []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`s]) [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj
                (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1"))
                "."
                `Preimage)
               [(Term.hole "_")]))
             [])
            (group (Tactic.continuity "continuity" []) [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
            (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
            (group
             (Tactic.rintro
              "rintro"
              [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
               (Tactic.rintroPat.one
                (Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `T)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hT)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                 "⟩"))]
              [])
             [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.hole "_")
                ","
                (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`T "," `hT] "⟩") "," `rfl] "⟩")
                ","
                (Term.hole "_")]
               "⟩"))
             [])
            (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
            (group
             (tacticRwa__
              "rwa"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule
                 ["←"]
                 (Term.proj (Term.app `hV [(Term.anonymousCtor "⟨" [`T "," `hT] "⟩")]) "." (fieldIdx "2")))]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `G)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hG)]) [])]
             "⟩")])]
         []
         [":=" [`this]])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j0)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj0)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `is_cofiltered.inf_objs_exists [(Term.app `G.image [`j])])]])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `f
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])
               (Term.simpleBinder [`hs] [(Term.typeSpec ":" (Init.Core.«term_∈_» `s " ∈ " `G))])]
              ","
              (Topology.Sequences.«term_⟶_» `j0 " ⟶ " (Term.app `j [`s]))))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s `hs] [])]
             "=>"
             (Term.proj
              (Term.app `hj0 [(Term.app `finset.mem_image.mpr [(Term.anonymousCtor "⟨" [`s "," `hs "," `rfl] "⟩")])])
              "."
              `some))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `W
           [(Term.typeSpec ":" (Term.arrow `S "→" (Term.app `Set [(Term.app `F.obj [`j0])])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`s] [])]
             "=>"
             (termDepIfThenElse
              "if"
              `hs
              ":"
              (Init.Core.«term_∈_» `s " ∈ " `G)
              "then"
              (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `F.map [(Term.app `f [`s `hs])]) " ⁻¹' " (Term.app `V [`s]))
              "else"
              `Set.Univ))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`j0
           ","
           (Set.Data.Set.Lattice.«term⋃_,_»
            "⋃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `s)] ":" `S ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hs)] ":" (Init.Core.«term_∈_» `s " ∈ " `G) ")")])
            ", "
            (Term.app `W [`s]))
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.apply "apply" `is_clopen_bUnion) [])
            (group (Tactic.intro "intro" [`s `hs]) [])
            (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `W)] "]"] [] []) [])
            (group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))] "]") [])
             [])
            (group
             (Tactic.«tactic_<;>_»
              (Tactic.refine'
               "refine'"
               (Term.anonymousCtor
                "⟨"
                [(Term.app
                  (Term.proj
                   (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1"))
                   "."
                   `Preimage)
                  [(Term.hole "_")])
                 ","
                 (Term.app
                  (Term.proj
                   (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2"))
                   "."
                   `Preimage)
                  [(Term.hole "_")])]
                "⟩"))
              "<;>"
              (Tactic.continuity "continuity" []))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
            (group (Tactic.constructor "constructor") [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`hx]) [])
                 (group
                  (Tactic.simpRw
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)]
                    "]")
                   [])
                  [])
                 (group
                  (Tactic.obtain
                   "obtain"
                   [(Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                        ","
                        (Tactic.rcasesPatLo
                         (Tactic.rcasesPatMed
                          [(Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                            "⟩")])
                         [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                        ","
                        (Tactic.rcasesPatLo
                         (Tactic.rcasesPatMed
                          [(Tactic.rcasesPat.tuple
                            "⟨"
                            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                             ","
                             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                            "⟩")])
                         [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hh)]) [])]
                       "⟩")])]
                   []
                   [":=" [(Term.app `hG [`hx])]])
                  [])
                 (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩")) [])
                 (group
                  (Tactic.dsimp
                   "dsimp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `W)] "]"]
                   []
                   [(Tactic.location "at" (Tactic.locationHyp [`hh] ["⊢"]))])
                  [])
                 (group
                  (tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
                     ","
                     (Tactic.rwRule ["←"] `Set.preimage_comp)
                     ","
                     (Tactic.rwRule ["←"] `Profinite.coe_comp)
                     ","
                     (Tactic.rwRule [] `C.w)]
                    "]")
                   [])
                  [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`hx]) [])
                 (group
                  (Tactic.simpRw
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                  [])
                 (group
                  (Tactic.obtain
                   "obtain"
                   [(Tactic.rcasesPatMed
                     [(Tactic.rcasesPat.tuple
                       "⟨"
                       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                        ","
                        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                       "⟩")])]
                   []
                   [":=" [`hx]])
                  [])
                 (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
                 (group
                  (Tactic.refine'
                   "refine'"
                   (Term.anonymousCtor
                    "⟨"
                    [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
                    "⟩"))
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2")))] "]")
                   [])
                  [])
                 (group
                  (Tactic.dsimp
                   "dsimp"
                   []
                   ["only"]
                   ["[" [(Tactic.simpLemma [] [] `W)] "]"]
                   []
                   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                  [])
                 (group
                  (tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
                     ","
                     (Tactic.rwRule ["←"] `Set.preimage_comp)
                     ","
                     (Tactic.rwRule ["←"] `Profinite.coe_comp)
                     ","
                     (Tactic.rwRule [] `C.w)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                  [])])))
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hB []]
          []
          ":="
          (Term.app
           `Top.is_topological_basis_cofiltered_limit
           [(CategoryTheory.Functor.CategoryTheory.Functor.«term_⋙_» `F " ⋙ " `Profinite.toTop)
            (Term.app `Profinite.to_Top.map_cone [`C])
            (Term.app `is_limit_of_preserves [(Term.hole "_") `hC])
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`j] [])]
              "=>"
              (Set.«term{_|_}» "{" `W "|" (Term.app `IsClopen [`W]) "}")))
            (Term.hole "_")
            (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" `is_clopen_univ))
            (Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`i `U1 `U2 `hU1 `hU2] [])] "=>" (Term.app `hU1.inter [`hU2])))
            (Term.hole "_")]))))
       [])
      (group (Tactic.rotate "rotate" []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`i]) [])
           (group
            (Tactic.change
             "change"
             (Term.app
              `TopologicalSpace.IsTopologicalBasis
              [(Set.«term{_|_}»
                "{"
                (Mathlib.ExtendedBinder.extBinder `W [":" (Term.app `Set [(Term.app `F.obj [`i])])])
                "|"
                (Term.app `IsClopen [`W])
                "}")])
             [])
            [])
           (group (Tactic.apply "apply" `is_topological_basis_clopen) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.one `i))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `j))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `f))
              (Tactic.rintroPat.one (Tactic.rcasesPat.one `V))
              (Tactic.rintroPat.one
               (Tactic.rcasesPat.paren
                "("
                (Tactic.rcasesPatLo
                 (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hV)])
                 [":" (Term.app `IsClopen [(Term.hole "_")])])
                ")"))]
             [])
            [])
           (group
            (Tactic.«tactic_<;>_»
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app (Term.proj (Term.proj `hV "." (fieldIdx "1")) "." `Preimage) [(Term.hole "_")])
                ","
                (Term.app (Term.proj (Term.proj `hV "." (fieldIdx "2")) "." `Preimage) [(Term.hole "_")])]
               "⟩"))
             "<;>"
             (Tactic.continuity "continuity" []))
            [])])))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `S)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hS)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `h)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `hB.open_eq_sUnion [(Term.proj `hU "." (fieldIdx "1"))])]])
       [])
      (group (Tactic.clear "clear" [`hB]) [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `j
          [(Term.typeSpec ":" (Term.arrow `S "→" `J))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `V
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
             ","
             (Term.app `Set [(Term.app `F.obj [(Term.app `j [`s])])])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (Term.proj (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some_spec) "." `some))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hV []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
             ","
             («term_∧_»
              (Term.app `IsClopen [(Term.app `V [`s])])
              "∧"
              («term_=_»
               (Term.proj `s "." (fieldIdx "1"))
               "="
               (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `C.π.app [(Term.app `j [`s])]) " ⁻¹' " (Term.app `V [`s]))))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (Term.proj
             (Term.proj (Term.app `hS [(Term.proj `s "." (fieldIdx "2"))]) "." `some_spec)
             "."
             `some_spec))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          []
          ":="
          (Term.app
           (Term.proj (Term.proj (Term.proj `hU "." (fieldIdx "2")) "." `IsCompact) "." `elim_finite_subcover)
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])]
              "=>"
              (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `C.π.app [(Term.app `j [`s])]) " ⁻¹' " (Term.app `V [`s]))))
            (Term.hole "_")
            (Term.hole "_")]))))
       [])
      (group (Tactic.rotate "rotate" []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`s]) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj
               (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1"))
               "."
               `Preimage)
              [(Term.hole "_")]))
            [])
           (group (Tactic.continuity "continuity" []) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
           (group
            (Tactic.rintro
             "rintro"
             [(Tactic.rintroPat.one (Tactic.rcasesPat.one `x))
              (Tactic.rintroPat.one
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `T)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hT)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                "⟩"))]
             [])
            [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.hole "_")
               ","
               (Term.anonymousCtor "⟨" [(Term.anonymousCtor "⟨" [`T "," `hT] "⟩") "," `rfl] "⟩")
               ","
               (Term.hole "_")]
              "⟩"))
            [])
           (group (Tactic.dsimp "dsimp" [] ["only"] [] [] []) [])
           (group
            (tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                ["←"]
                (Term.proj (Term.app `hV [(Term.anonymousCtor "⟨" [`T "," `hT] "⟩")]) "." (fieldIdx "2")))]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `G)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hG)]) [])]
            "⟩")])]
        []
        [":=" [`this]])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `j0)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hj0)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `is_cofiltered.inf_objs_exists [(Term.app `G.image [`j])])]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `f
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`s] [(Term.typeSpec ":" `S)])
              (Term.simpleBinder [`hs] [(Term.typeSpec ":" (Init.Core.«term_∈_» `s " ∈ " `G))])]
             ","
             (Topology.Sequences.«term_⟶_» `j0 " ⟶ " (Term.app `j [`s]))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s `hs] [])]
            "=>"
            (Term.proj
             (Term.app `hj0 [(Term.app `finset.mem_image.mpr [(Term.anonymousCtor "⟨" [`s "," `hs "," `rfl] "⟩")])])
             "."
             `some))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `W
          [(Term.typeSpec ":" (Term.arrow `S "→" (Term.app `Set [(Term.app `F.obj [`j0])])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`s] [])]
            "=>"
            (termDepIfThenElse
             "if"
             `hs
             ":"
             (Init.Core.«term_∈_» `s " ∈ " `G)
             "then"
             (Set.Data.Set.Basic.«term_⁻¹'_» (Term.app `F.map [(Term.app `f [`s `hs])]) " ⁻¹' " (Term.app `V [`s]))
             "else"
             `Set.Univ))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`j0
          ","
          (Set.Data.Set.Lattice.«term⋃_,_»
           "⋃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `s)] ":" `S ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hs)] ":" (Init.Core.«term_∈_» `s " ∈ " `G) ")")])
           ", "
           (Term.app `W [`s]))
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.apply "apply" `is_clopen_bUnion) [])
           (group (Tactic.intro "intro" [`s `hs]) [])
           (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `W)] "]"] [] []) [])
           (group
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))] "]") [])
            [])
           (group
            (Tactic.«tactic_<;>_»
             (Tactic.refine'
              "refine'"
              (Term.anonymousCtor
               "⟨"
               [(Term.app
                 (Term.proj
                  (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1"))
                  "."
                  `Preimage)
                 [(Term.hole "_")])
                ","
                (Term.app
                 (Term.proj
                  (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2"))
                  "."
                  `Preimage)
                 [(Term.hole "_")])]
               "⟩"))
             "<;>"
             (Tactic.continuity "continuity" []))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
           (group (Tactic.constructor "constructor") [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`hx]) [])
                (group
                 (Tactic.simpRw
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)]
                   "]")
                  [])
                 [])
                (group
                 (Tactic.obtain
                  "obtain"
                  [(Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                       ","
                       (Tactic.rcasesPatLo
                        (Tactic.rcasesPatMed
                         [(Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                           "⟩")])
                        [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                       ","
                       (Tactic.rcasesPatLo
                        (Tactic.rcasesPatMed
                         [(Tactic.rcasesPat.tuple
                           "⟨"
                           [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                            ","
                            (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                           "⟩")])
                        [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hh)]) [])]
                      "⟩")])]
                  []
                  [":=" [(Term.app `hG [`hx])]])
                 [])
                (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩")) [])
                (group
                 (Tactic.dsimp
                  "dsimp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `W)] "]"]
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`hh] ["⊢"]))])
                 [])
                (group
                 (tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
                    ","
                    (Tactic.rwRule ["←"] `Set.preimage_comp)
                    ","
                    (Tactic.rwRule ["←"] `Profinite.coe_comp)
                    ","
                    (Tactic.rwRule [] `C.w)]
                   "]")
                  [])
                 [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`hx]) [])
                (group
                 (Tactic.simpRw
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                 [])
                (group
                 (Tactic.obtain
                  "obtain"
                  [(Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                      "⟩")])]
                  []
                  [":=" [`hx]])
                 [])
                (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
                (group
                 (Tactic.refine'
                  "refine'"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
                   "⟩"))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2")))] "]")
                  [])
                 [])
                (group
                 (Tactic.dsimp
                  "dsimp"
                  []
                  ["only"]
                  ["[" [(Tactic.simpLemma [] [] `W)] "]"]
                  []
                  [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                 [])
                (group
                 (tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
                    ","
                    (Tactic.rwRule ["←"] `Set.preimage_comp)
                    ","
                    (Tactic.rwRule ["←"] `Profinite.coe_comp)
                    ","
                    (Tactic.rwRule [] `C.w)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                 [])])))
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
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] []) [])
      (group (Tactic.constructor "constructor") [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`hx]) [])
           (group
            (Tactic.simpRw
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
             [])
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                  ","
                  (Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                      "⟩")])
                   [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
                  ","
                  (Tactic.rcasesPatLo
                   (Tactic.rcasesPatMed
                    [(Tactic.rcasesPat.tuple
                      "⟨"
                      [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                       ","
                       (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                      "⟩")])
                   [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hh)]) [])]
                 "⟩")])]
             []
             [":=" [(Term.app `hG [`hx])]])
            [])
           (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩")) [])
           (group
            (Tactic.dsimp
             "dsimp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `W)] "]"]
             []
             [(Tactic.location "at" (Tactic.locationHyp [`hh] ["⊢"]))])
            [])
           (group
            (tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
               ","
               (Tactic.rwRule ["←"] `Set.preimage_comp)
               ","
               (Tactic.rwRule ["←"] `Profinite.coe_comp)
               ","
               (Tactic.rwRule [] `C.w)]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`hx]) [])
           (group
            (Tactic.simpRw
             "simp_rw"
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
                 "⟩")])]
             []
             [":=" [`hx]])
            [])
           (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
           (group
            (Tactic.refine'
             "refine'"
             (Term.anonymousCtor
              "⟨"
              [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
              "⟩"))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2")))] "]")
             [])
            [])
           (group
            (Tactic.dsimp
             "dsimp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `W)] "]"]
             []
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            [])
           (group
            (tacticRwa__
             "rwa"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
               ","
               (Tactic.rwRule ["←"] `Set.preimage_comp)
               ","
               (Tactic.rwRule ["←"] `Profinite.coe_comp)
               ","
               (Tactic.rwRule [] `C.w)]
              "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
            [])])))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
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
     [(group (Tactic.intro "intro" [`hx]) [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
            "⟩")])]
        []
        [":=" [`hx]])
       [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") []) [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2")))] "]")
        [])
       [])
      (group
       (Tactic.dsimp
        "dsimp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `W)] "]"]
        []
        [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
       [])
      (group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
          ","
          (Tactic.rwRule ["←"] `Set.preimage_comp)
          ","
          (Tactic.rwRule ["←"] `Profinite.coe_comp)
          ","
          (Tactic.rwRule [] `C.w)]
         "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
     ","
     (Tactic.rwRule ["←"] `Set.preimage_comp)
     ","
     (Tactic.rwRule ["←"] `Profinite.coe_comp)
     ","
     (Tactic.rwRule [] `C.w)]
    "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C.w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Profinite.coe_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.preimage_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dif_pos [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dif_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp
   "dsimp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `W)] "]"]
   []
   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `W
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
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2")))] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `hV [`s]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`s])
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
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`s]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.proj `s "." (fieldIdx "1")) "," (Term.proj `s "." (fieldIdx "2")) "," (Term.hole "_")]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj `s "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])]
       "⟩")])]
   []
   [":=" [`hx]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.preimage_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`hx]) [])
      (group
       (Tactic.simpRw
        "simp_rw"
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
        [])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩")])
              [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
             ","
             (Tactic.rcasesPatLo
              (Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
                 "⟩")])
              [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hh)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `hG [`hx])]])
       [])
      (group (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩")) [])
      (group
       (Tactic.dsimp
        "dsimp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `W)] "]"]
        []
        [(Tactic.location "at" (Tactic.locationHyp [`hh] ["⊢"]))])
       [])
      (group
       (tacticRwa__
        "rwa"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
          ","
          (Tactic.rwRule ["←"] `Set.preimage_comp)
          ","
          (Tactic.rwRule ["←"] `Profinite.coe_comp)
          ","
          (Tactic.rwRule [] `C.w)]
         "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))
     ","
     (Tactic.rwRule ["←"] `Set.preimage_comp)
     ","
     (Tactic.rwRule ["←"] `Profinite.coe_comp)
     ","
     (Tactic.rwRule [] `C.w)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C.w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Profinite.coe_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.preimage_comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dif_pos [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dif_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp
   "dsimp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `W)] "]"]
   []
   [(Tactic.location "at" (Tactic.locationHyp [`hh] ["⊢"]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«⊢»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hh
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine' "refine'" (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor "⟨" [`s "," `hs "," (Term.hole "_")] "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
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
  (Tactic.obtain
   "obtain"
   [(Tactic.rcasesPatMed
     [(Tactic.rcasesPat.tuple
       "⟨"
       [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
        ","
        (Tactic.rcasesPatLo
         (Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `s)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])
         [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.ignore "_")]) [])
        ","
        (Tactic.rcasesPatLo
         (Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hs)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])
         [])
        ","
        (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hh)]) [])]
       "⟩")])]
   []
   [":=" [(Term.app `hG [`hx])]])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.obtain', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `hG [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `hG
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatMed', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.tuple', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPatLo', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.ignore', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw
   "simp_rw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Set.preimage_Union) "," (Tactic.rwRule [] `Set.mem_Union)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.preimage_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.constructor "constructor")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.constructor', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `x)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.apply "apply" `is_clopen_bUnion) [])
      (group (Tactic.intro "intro" [`s `hs]) [])
      (group (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `W)] "]"] [] []) [])
      (group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))] "]") []) [])
      (group
       (Tactic.«tactic_<;>_»
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.app
            (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
            [(Term.hole "_")])
           ","
           (Term.app
            (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
            [(Term.hole "_")])]
          "⟩"))
        "<;>"
        (Tactic.continuity "continuity" []))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.«tactic_<;>_»
   (Tactic.refine'
    "refine'"
    (Term.anonymousCtor
     "⟨"
     [(Term.app
       (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
       [(Term.hole "_")])
      ","
      (Term.app
       (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
       [(Term.hole "_")])]
     "⟩"))
   "<;>"
   (Tactic.continuity "continuity" []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic_<;>_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.continuity "continuity" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.continuity', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [(Term.app
      (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
      [(Term.hole "_")])
     ","
     (Term.app
      (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
      [(Term.hole "_")])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app
     (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
     [(Term.hole "_")])
    ","
    (Term.app
     (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
     [(Term.hole "_")])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
   [(Term.hole "_")])
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
  (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2")) "." `Preimage)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`s])
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
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`s]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
   [(Term.hole "_")])
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
  (Term.proj (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1")) "." `Preimage)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1")) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `hV [`s]) "." (fieldIdx "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `hV [`s])
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
  `hV
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `hV [`s]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `dif_pos [`hs]))] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `dif_pos [`hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `dif_pos
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `W)] "]"] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`s `hs])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hs
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `is_clopen_bUnion)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `is_clopen_bUnion
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.anonymousCtor
    "⟨"
    [`j0
     ","
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `s)] ":" `S ")")
        (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hs)] ":" (Init.Core.«term_∈_» `s " ∈ " `G) ")")])
      ", "
      (Term.app `W [`s]))
     ","
     (Term.hole "_")
     ","
     (Term.hole "_")]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [`j0
    ","
    (Set.Data.Set.Lattice.«term⋃_,_»
     "⋃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `s)] ":" `S ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hs)] ":" (Init.Core.«term_∈_» `s " ∈ " `G) ")")])
     ", "
     (Term.app `W [`s]))
    ","
    (Term.hole "_")
    ","
    (Term.hole "_")]
   "⟩")
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `s)] ":" `S ")")
     (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hs)] ":" (Init.Core.«term_∈_» `s " ∈ " `G) ")")])
   ", "
   (Term.app `W [`s]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `W [`s])
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
  `W
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
    If `X` is a cofiltered limit of profinite sets, then any clopen subset of `X` arises from
    a clopen set in one of the terms in the limit.
    -/
  theorem
    exists_clopen_of_cofiltered
    { U : Set C.X } ( hU : IsClopen U ) : ∃ ( j : J ) ( V : Set F.obj j ) ( hV : IsClopen V ) , U = C.π.app j ⁻¹' V
    :=
      by
        have
            hB
              :=
              Top.is_topological_basis_cofiltered_limit
                F ⋙ Profinite.toTop
                  Profinite.to_Top.map_cone C
                  is_limit_of_preserves _ hC
                  fun j => { W | IsClopen W }
                  _
                  fun i => is_clopen_univ
                  fun i U1 U2 hU1 hU2 => hU1.inter hU2
                  _
          rotate
          ·
            intro i
              change TopologicalSpace.IsTopologicalBasis { W : Set F.obj i | IsClopen W }
              apply is_topological_basis_clopen
          · rintro i j f V ( hV : IsClopen _ ) refine' ⟨ hV . 1 . Preimage _ , hV . 2 . Preimage _ ⟩ <;> continuity
          obtain ⟨ S , hS , h ⟩ := hB.open_eq_sUnion hU . 1
          clear hB
          let j : S → J := fun s => hS s . 2 . some
          let V : ∀ s : S , Set F.obj j s := fun s => hS s . 2 . some_spec . some
          have hV : ∀ s : S , IsClopen V s ∧ s . 1 = C.π.app j s ⁻¹' V s := fun s => hS s . 2 . some_spec . some_spec
          have := hU . 2 . IsCompact . elim_finite_subcover fun s : S => C.π.app j s ⁻¹' V s _ _
          rotate
          · intro s refine' hV s . 1 . 1 . Preimage _ continuity
          ·
            dsimp only
              rw [ h ]
              rintro x ⟨ T , hT , hx ⟩
              refine' ⟨ _ , ⟨ ⟨ T , hT ⟩ , rfl ⟩ , _ ⟩
              dsimp only
              rwa [ ← hV ⟨ T , hT ⟩ . 2 ]
          obtain ⟨ G , hG ⟩ := this
          obtain ⟨ j0 , hj0 ⟩ := is_cofiltered.inf_objs_exists G.image j
          let f : ∀ s : S hs : s ∈ G , j0 ⟶ j s := fun s hs => hj0 finset.mem_image.mpr ⟨ s , hs , rfl ⟩ . some
          let W : S → Set F.obj j0 := fun s => if hs : s ∈ G then F.map f s hs ⁻¹' V s else Set.Univ
          refine' ⟨ j0 , ⋃ ( s : S ) ( hs : s ∈ G ) , W s , _ , _ ⟩
          ·
            apply is_clopen_bUnion
              intro s hs
              dsimp only [ W ]
              rw [ dif_pos hs ]
              refine' ⟨ hV s . 1 . 1 . Preimage _ , hV s . 1 . 2 . Preimage _ ⟩ <;> continuity
          ·
            ext x
              constructor
              ·
                intro hx
                  simp_rw [ Set.preimage_Union , Set.mem_Union ]
                  obtain ⟨ _ , ⟨ s , rfl ⟩ , _ , ⟨ hs , rfl ⟩ , hh ⟩ := hG hx
                  refine' ⟨ s , hs , _ ⟩
                  dsimp only [ W ] at hh ⊢
                  rwa [ dif_pos hs , ← Set.preimage_comp , ← Profinite.coe_comp , C.w ]
              ·
                intro hx
                  simp_rw [ Set.preimage_Union , Set.mem_Union ] at hx
                  obtain ⟨ s , hs , hx ⟩ := hx
                  rw [ h ]
                  refine' ⟨ s . 1 , s . 2 , _ ⟩
                  rw [ hV s . 2 ]
                  dsimp only [ W ] at hx
                  rwa [ dif_pos hs , ← Set.preimage_comp , ← Profinite.coe_comp , C.w ] at hx

theorem exists_locally_constant_fin_two (f : LocallyConstant C.X (Finₓ 2)) :
    ∃ (j : J)(g : LocallyConstant (F.obj j) (Finₓ 2)), f = g.comap (C.π.app _) := by
  let U := f ⁻¹' {0}
  have hU : IsClopen U := f.is_locally_constant.is_clopen_fiber _
  obtain ⟨j, V, hV, h⟩ := exists_clopen_of_cofiltered C hC hU
  use j, LocallyConstant.ofClopen hV
  apply LocallyConstant.locally_constant_eq_of_fiber_zero_eq
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  conv_rhs => rw [Set.preimage_comp]
  rw [LocallyConstant.of_clopen_fiber_zero hV, ← h]

theorem exists_locally_constant_fintype_aux {α : Type _} [Fintype α] (f : LocallyConstant C.X α) :
    ∃ (j : J)(g : LocallyConstant (F.obj j) (α → Finₓ 2)),
      (f.map fun a b => if a = b then (0 : Finₓ 2) else 1) = g.comap (C.π.app _) :=
  by
  let ι : α → α → Finₓ 2 := fun x y => if x = y then 0 else 1
  let ff := (f.map ι).flip
  have hff := fun a : α => exists_locally_constant_fin_two _ hC (ff a)
  choose j g h using hff
  let G : Finset J := finset.univ.image j
  obtain ⟨j0, hj0⟩ := is_cofiltered.inf_objs_exists G
  have hj : ∀ a, j a ∈ G := by
    intro a
    simp [G]
  let fs : ∀ a : α, j0 ⟶ j a := fun a => (hj0 (hj a)).some
  let gg : α → LocallyConstant (F.obj j0) (Finₓ 2) := fun a => (g a).comap (F.map (fs _))
  let ggg := LocallyConstant.unflip gg
  refine' ⟨j0, ggg, _⟩
  have : f.map ι = LocallyConstant.unflip (f.map ι).flip := by
    simp
  rw [this]
  clear this
  have :
    LocallyConstant.comap (C.π.app j0) ggg = LocallyConstant.unflip (LocallyConstant.comap (C.π.app j0) ggg).flip := by
    simp
  rw [this]
  clear this
  congr 1
  ext1 a
  change ff a = _
  rw [h]
  dsimp [ggg, gg]
  ext1
  repeat'
    rw [LocallyConstant.coe_comap]
    dsimp [LocallyConstant.flip, LocallyConstant.unflip]
  ·
    congr 1
    change _ = (C.π.app j0 ≫ F.map (fs a)) x
    rw [C.w]
  all_goals
    continuity

theorem exists_locally_constant_fintype_nonempty {α : Type _} [Fintype α] [Nonempty α] (f : LocallyConstant C.X α) :
    ∃ (j : J)(g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  inhabit α
  obtain ⟨j, gg, h⟩ := exists_locally_constant_fintype_aux _ hC f
  let ι : α → α → Finₓ 2 := fun a b => if a = b then 0 else 1
  let σ : (α → Finₓ 2) → α := fun f => if h : ∃ a : α, ι a = f then h.some else arbitraryₓ _
  refine' ⟨j, gg.map σ, _⟩
  ext
  rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  dsimp [σ]
  have h1 : ι (f x) = gg (C.π.app j x) := by
    change f.map (fun a b => if a = b then (0 : Finₓ 2) else 1) x = _
    rw [h, LocallyConstant.coe_comap _ _ (C.π.app j).Continuous]
  have h2 : ∃ a : α, ι a = gg (C.π.app j x) := ⟨f x, h1⟩
  rw [dif_pos h2]
  apply_fun ι
  ·
    rw [h2.some_spec]
    exact h1
  ·
    intro a b hh
    apply_fun fun e => e a  at hh
    dsimp [ι]  at hh
    rw [if_pos rfl] at hh
    split_ifs  at hh with hh1 hh1
    ·
      exact hh1.symm
    ·
      exact False.elim (bot_ne_top hh)

/--  Any locally constant function from a cofiltered limit of profinite sets factors through
one of the components. -/
theorem exists_locally_constant {α : Type _} (f : LocallyConstant C.X α) :
    ∃ (j : J)(g : LocallyConstant (F.obj j) α), f = g.comap (C.π.app _) := by
  let S := f.discrete_quotient
  let ff : S → α := f.lift
  cases' is_empty_or_nonempty S
  ·
    suffices ∃ j, IsEmpty (F.obj j)by
      refine' this.imp fun j hj => _
      refine' ⟨⟨hj.elim, fun A => _⟩, _⟩
      ·
        convert is_open_empty
        exact @Set.eq_empty_of_is_empty _ hj _
      ·
        ext x
        exact hj.elim' (C.π.app j x)
    simp only [← not_nonempty_iff, ← not_forall]
    intro h
    have : ∀ j : J, Nonempty ((F ⋙ Profinite.toTop).obj j) := h
    have : ∀ j : J, T2Space ((F ⋙ Profinite.toTop).obj j) := fun j => (inferInstance : T2Space (F.obj j))
    have : ∀ j : J, CompactSpace ((F ⋙ Profinite.toTop).obj j) := fun j => (inferInstance : CompactSpace (F.obj j))
    have cond := Top.nonempty_limit_cone_of_compact_t2_cofiltered_system (F ⋙ Profinite.toTop)
    suffices : Nonempty C.X
    exact IsEmpty.false (S.proj this.some)
    let D := Profinite.to_Top.map_cone C
    have hD : is_limit D := is_limit_of_preserves Profinite.toTop hC
    have CD := (hD.cone_point_unique_up_to_iso (Top.limitConeIsLimit _)).inv
    exact cond.map CD
  ·
    let f' : LocallyConstant C.X S := ⟨S.proj, S.proj_is_locally_constant⟩
    obtain ⟨j, g', hj⟩ := exists_locally_constant_fintype_nonempty _ hC f'
    refine' ⟨j, ⟨ff ∘ g', g'.is_locally_constant.comp _⟩, _⟩
    ext1 t
    apply_fun fun e => e t  at hj
    rw [LocallyConstant.coe_comap _ _ (C.π.app j).Continuous] at hj⊢
    dsimp  at hj⊢
    rw [← hj]
    rfl

end Profinite

