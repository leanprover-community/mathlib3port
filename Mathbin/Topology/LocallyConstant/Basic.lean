/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Topology.SubsetProperties
import Mathbin.Topology.Connected
import Mathbin.Topology.Algebra.Monoid
import Mathbin.Topology.ContinuousFunction.Basic
import Mathbin.Tactic.Tfae
import Mathbin.Tactic.FinCases

/-!
# Locally constant functions

This file sets up the theory of locally constant function from a topological space to a type.

## Main definitions and constructions

* `is_locally_constant f` : a map `f : X → Y` where `X` is a topological space is locally
                            constant if every set in `Y` has an open preimage.
* `locally_constant X Y` : the type of locally constant maps from `X` to `Y`
* `locally_constant.map` : push-forward of locally constant maps
* `locally_constant.comap` : pull-back of locally constant maps

-/


variable {X Y Z α : Type _} [TopologicalSpace X]

open Set Filter

open TopologicalSpace

/-- A function between topological spaces is locally constant if the preimage of any set is open. -/
def IsLocallyConstant (f : X → Y) : Prop :=
  ∀ s : Set Y, IsOpen (f ⁻¹' s)

namespace IsLocallyConstant

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers [] [] [(Command.protected "protected")] [] [] [])
     (Command.theorem
      "theorem"
      (Command.declId `tfae [])
      (Command.declSig
       [(Term.explicitBinder "(" [`f] [":" (Term.arrow `X "→" `Y)] [] ")")]
       (Term.typeSpec
        ":"
        (Term.app
         `Tfae
         [(«term[_]»
           "["
           [(Term.app `IsLocallyConstant [`f])
            ","
            (Term.forall
             "∀"
             [`x]
             []
             ","
             (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
              "∀ᶠ"
              (Std.ExtendedBinder.extBinders (Std.ExtendedBinder.extBinder (Lean.binderIdent `x') []))
              " in "
              (Term.app (TopologicalSpace.Topology.Basic.nhds "𝓝") [`x])
              ", "
              («term_=_» (Term.app `f [`x']) "=" (Term.app `f [`x]))))
            ","
            (Term.forall
             "∀"
             [`x]
             []
             ","
             (Term.app
              `IsOpen
              [(Set.«term{_|_}»
                "{"
                (Std.ExtendedBinder.extBinder (Lean.binderIdent `x') [])
                "|"
                («term_=_» (Term.app `f [`x']) "=" (Term.app `f [`x]))
                "}")]))
            ","
            (Term.forall
             "∀"
             [`y]
             []
             ","
             (Term.app `IsOpen [(Set.Data.Set.Basic.«term_⁻¹'_» `f " ⁻¹' " («term{_}» "{" [`y] "}"))]))
            ","
            (Term.forall
             "∀"
             [`x]
             []
             ","
             («term∃_,_»
              "∃"
              (Lean.explicitBinders
               [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `U)] ":" (Term.app `Set [`X]) ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hU)] ":" (Term.app `IsOpen [`U]) ")")
                (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hx)] ":" («term_∈_» `x "∈" `U) ")")])
              ","
              (Std.ExtendedBinder.«term∀__,_»
               "∀"
               (Lean.binderIdent `x')
               («binderTerm∈_» "∈" `U)
               ","
               («term_=_» (Term.app `f [`x']) "=" (Term.app `f [`x])))))]
           "]")])))
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
           []
           (Tactic.exact
            "exact"
            (Term.fun "fun" (Term.basicFun [`h `y] [] "=>" (Term.app `h [(«term{_}» "{" [`y] "}")]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
           []
           (Tactic.exact "exact" (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `h [(Term.app `f [`x])]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
           []
           (Tactic.exact
            "exact"
            (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `IsOpen.mem_nhds [(Term.app `h [`x]) `rfl]))))
           []
           (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "5"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group (Tactic.intro "intro" [`h `x]) [])
             (group
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app (Term.proj `mem_nhds_iff "." (fieldIdx "1")) [(Term.app `h [`x])]))]
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
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                      [])]
                    "⟩")])
                 [])])
              [])
             (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`U "," `hU "," `hx "," `Eq] "⟩")) [])])
           []
           (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
           []
           («tactic___;_»
            (cdotTk (patternIgnore (token.«·» "·")))
            [(group (Tactic.intro "intro" [`h `s]) [])
             (group
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
                [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))]))
              [])
             (group
              (Std.Tactic.rcases
               "rcases"
               [(Tactic.casesTarget [] (Term.app `h [`x]))]
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
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxU)])
                      [])
                     ","
                     (Std.Tactic.RCases.rcasesPatLo
                      (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                      [])]
                    "⟩")])
                 [])])
              [])
             (group
              (Tactic.exact
               "exact"
               (Term.anonymousCtor
                "⟨"
                [`U
                 ","
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [`x' `hx']
                   []
                   "=>"
                   («term_<|_»
                    (Term.proj `mem_preimage "." (fieldIdx "2"))
                    "<|"
                    (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
                 ","
                 `hU
                 ","
                 `hxU]
                "⟩"))
              [])])
           []
           (Tactic.tfaeFinish "tfae_finish")])))
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
         [(Tactic.tfaeHave "tfae_have" [] (num "1") "→" (num "4"))
          []
          (Tactic.exact
           "exact"
           (Term.fun "fun" (Term.basicFun [`h `y] [] "=>" (Term.app `h [(«term{_}» "{" [`y] "}")]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "4") "→" (num "3"))
          []
          (Tactic.exact "exact" (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `h [(Term.app `f [`x])]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "3") "→" (num "2"))
          []
          (Tactic.exact
           "exact"
           (Term.fun "fun" (Term.basicFun [`h `x] [] "=>" (Term.app `IsOpen.mem_nhds [(Term.app `h [`x]) `rfl]))))
          []
          (Tactic.tfaeHave "tfae_have" [] (num "2") "→" (num "5"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" [`h `x]) [])
            (group
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app (Term.proj `mem_nhds_iff "." (fieldIdx "1")) [(Term.app `h [`x])]))]
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
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hx)])
                     [])]
                   "⟩")])
                [])])
             [])
            (group (Tactic.exact "exact" (Term.anonymousCtor "⟨" [`U "," `hU "," `hx "," `Eq] "⟩")) [])])
          []
          (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group (Tactic.intro "intro" [`h `s]) [])
            (group
             (Tactic.refine'
              "refine'"
              (Term.app
               (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
               [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))]))
             [])
            (group
             (Std.Tactic.rcases
              "rcases"
              [(Tactic.casesTarget [] (Term.app `h [`x]))]
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
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxU)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                     [])]
                   "⟩")])
                [])])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`U
                ","
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`x' `hx']
                  []
                  "=>"
                  («term_<|_»
                   (Term.proj `mem_preimage "." (fieldIdx "2"))
                   "<|"
                   (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
                ","
                `hU
                ","
                `hxU]
               "⟩"))
             [])])
          []
          (Tactic.tfaeFinish "tfae_finish")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeFinish "tfae_finish")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group (Tactic.intro "intro" [`h `s]) [])
        (group
         (Tactic.refine'
          "refine'"
          (Term.app
           (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
           [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))]))
         [])
        (group
         (Std.Tactic.rcases
          "rcases"
          [(Tactic.casesTarget [] (Term.app `h [`x]))]
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
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxU)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
                 [])]
               "⟩")])
            [])])
         [])
        (group
         (Tactic.exact
          "exact"
          (Term.anonymousCtor
           "⟨"
           [`U
            ","
            (Term.fun
             "fun"
             (Term.basicFun
              [`x' `hx']
              []
              "=>"
              («term_<|_»
               (Term.proj `mem_preimage "." (fieldIdx "2"))
               "<|"
               (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
            ","
            `hU
            ","
            `hxU]
           "⟩"))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.anonymousCtor
        "⟨"
        [`U
         ","
         (Term.fun
          "fun"
          (Term.basicFun
           [`x' `hx']
           []
           "=>"
           («term_<|_»
            (Term.proj `mem_preimage "." (fieldIdx "2"))
            "<|"
            (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
         ","
         `hU
         ","
         `hxU]
        "⟩"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [`U
        ","
        (Term.fun
         "fun"
         (Term.basicFun
          [`x' `hx']
          []
          "=>"
          («term_<|_»
           (Term.proj `mem_preimage "." (fieldIdx "2"))
           "<|"
           (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
        ","
        `hU
        ","
        `hxU]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hxU
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hU
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`x' `hx']
        []
        "=>"
        («term_<|_»
         (Term.proj `mem_preimage "." (fieldIdx "2"))
         "<|"
         (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj `mem_preimage "." (fieldIdx "2"))
       "<|"
       (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.subst (Term.proj (Term.app `Eq [`x' `hx']) "." `symm) "▸" [`hx])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 75 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 75, term))
      (Term.proj (Term.app `Eq [`x' `hx']) "." `symm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `Eq [`x' `hx'])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Eq [`x' `hx']) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 75, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 75, (some 75, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj `mem_preimage "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `mem_preimage
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `U
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Std.Tactic.rcases
       "rcases"
       [(Tactic.casesTarget [] (Term.app `h [`x]))]
       ["with"
        (Std.Tactic.RCases.rcasesPatLo
         (Std.Tactic.RCases.rcasesPatMed
          [(Std.Tactic.RCases.rcasesPat.tuple
            "⟨"
            [(Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `U)]) [])
             ","
             (Std.Tactic.RCases.rcasesPatLo (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hU)]) [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hxU)])
              [])
             ","
             (Std.Tactic.RCases.rcasesPatLo
              (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `eq)])
              [])]
            "⟩")])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [`x])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
        [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
       [(Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`x `hx] [] "=>" (Term.hole "_")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `hx
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `x
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `is_open_iff_forall_mem_open "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `is_open_iff_forall_mem_open
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.intro "intro" [`h `s])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `s
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tfaeHave "tfae_have" [] (num "5") "→" (num "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« → »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ↔ »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«→»', expected 'token.« ← »'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.theorem', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
protected
  theorem
    tfae
    ( f : X → Y )
      :
        Tfae
          [
            IsLocallyConstant f
              ,
              ∀ x , ∀ᶠ x' in 𝓝 x , f x' = f x
              ,
              ∀ x , IsOpen { x' | f x' = f x }
              ,
              ∀ y , IsOpen f ⁻¹' { y }
              ,
              ∀ x , ∃ ( U : Set X ) ( hU : IsOpen U ) ( hx : x ∈ U ) , ∀ x' ∈ U , f x' = f x
            ]
    :=
      by
        tfae_have 1 → 4
          exact fun h y => h { y }
          tfae_have 4 → 3
          exact fun h x => h f x
          tfae_have 3 → 2
          exact fun h x => IsOpen.mem_nhds h x rfl
          tfae_have 2 → 5
          · intro h x rcases mem_nhds_iff . 1 h x with ⟨ U , eq , hU , hx ⟩ exact ⟨ U , hU , hx , Eq ⟩
          tfae_have 5 → 1
          ·
            intro h s
              refine' is_open_iff_forall_mem_open . 2 fun x hx => _
              rcases h x with ⟨ U , hU , hxU , eq ⟩
              exact ⟨ U , fun x' hx' => mem_preimage . 2 <| Eq x' hx' . symm ▸ hx , hU , hxU ⟩
          tfae_finish

@[nontriviality]
theorem of_discrete [DiscreteTopology X] (f : X → Y) : IsLocallyConstant f := fun s => is_open_discrete _

theorem is_open_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsOpen { x | f x = y } :=
  hf {y}

theorem isClosedFiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClosed { x | f x = y } :=
  ⟨hf ({y}ᶜ)⟩

theorem is_clopen_fiber {f : X → Y} (hf : IsLocallyConstant f) (y : Y) : IsClopen { x | f x = y } :=
  ⟨is_open_fiber hf _, isClosedFiber hf _⟩

theorem iff_exists_open (f : X → Y) :
    IsLocallyConstant f ↔ ∀ x, ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
  (IsLocallyConstant.tfae f).out 0 4

theorem iff_eventually_eq (f : X → Y) : IsLocallyConstant f ↔ ∀ x, ∀ᶠ y in 𝓝 x, f y = f x :=
  (IsLocallyConstant.tfae f).out 0 1

theorem exists_open {f : X → Y} (hf : IsLocallyConstant f) (x : X) :
    ∃ (U : Set X)(hU : IsOpen U)(hx : x ∈ U), ∀ x' ∈ U, f x' = f x :=
  (iff_exists_open f).1 hf x

protected theorem eventually_eq {f : X → Y} (hf : IsLocallyConstant f) (x : X) : ∀ᶠ y in 𝓝 x, f y = f x :=
  (iff_eventually_eq f).1 hf x

protected theorem continuous [TopologicalSpace Y] {f : X → Y} (hf : IsLocallyConstant f) : Continuous f :=
  ⟨fun U hU => hf _⟩

theorem iff_continuous {_ : TopologicalSpace Y} [DiscreteTopology Y] (f : X → Y) : IsLocallyConstant f ↔ Continuous f :=
  ⟨IsLocallyConstant.continuous, fun h s => h.is_open_preimage s (is_open_discrete _)⟩

theorem iff_continuous_bot (f : X → Y) : IsLocallyConstant f ↔ @Continuous X Y _ ⊥ f :=
  iff_continuous f

theorem of_constant (f : X → Y) (h : ∀ x y, f x = f y) : IsLocallyConstant f :=
  (iff_eventually_eq f).2 fun x => eventually_of_forall fun x' => h _ _

theorem const (y : Y) : IsLocallyConstant (Function.const X y) :=
  (of_constant _) fun _ _ => rfl

theorem comp {f : X → Y} (hf : IsLocallyConstant f) (g : Y → Z) : IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf _

theorem prod_mk {Y'} {f : X → Y} {f' : X → Y'} (hf : IsLocallyConstant f) (hf' : IsLocallyConstant f') :
    IsLocallyConstant fun x => (f x, f' x) :=
  (iff_eventually_eq _).2 fun x => (hf.EventuallyEq x).mp <| (hf'.EventuallyEq x).mono fun x' hf' hf => Prod.ext hf hf'

theorem comp₂ {Y₁ Y₂ Z : Type _} {f : X → Y₁} {g : X → Y₂} (hf : IsLocallyConstant f) (hg : IsLocallyConstant g)
    (h : Y₁ → Y₂ → Z) : IsLocallyConstant fun x => h (f x) (g x) :=
  (hf.prod_mk hg).comp fun x : Y₁ × Y₂ => h x.1 x.2

theorem comp_continuous [TopologicalSpace Y] {g : Y → Z} {f : X → Y} (hg : IsLocallyConstant g) (hf : Continuous f) :
    IsLocallyConstant (g ∘ f) := fun s => by
  rw [Set.preimage_comp]
  exact hf.is_open_preimage _ (hg _)

/-- A locally constant function is constant on any preconnected set. -/
theorem apply_eq_of_is_preconnected {f : X → Y} (hf : IsLocallyConstant f) {s : Set X} (hs : IsPreconnected s) {x y : X}
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y := by
  let U := f ⁻¹' {f y}
  suffices : x ∉ Uᶜ
  exact not_not.1 this
  intro hxV
  specialize hs U (Uᶜ) (hf {f y}) (hf ({f y}ᶜ)) _ ⟨y, ⟨hy, rfl⟩⟩ ⟨x, ⟨hx, hxV⟩⟩
  · simp only [union_compl_self, subset_univ]
    
  · simpa only [inter_empty, not_nonempty_empty, inter_compl_self] using hs
    

theorem apply_eq_of_preconnected_space [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f) (x y : X) :
    f x = f y :=
  hf.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial

theorem eq_const [PreconnectedSpace X] {f : X → Y} (hf : IsLocallyConstant f) (x : X) : f = Function.const X (f x) :=
  funext fun y => hf.apply_eq_of_preconnected_space y x

theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] {f : X → Y} (hf : IsLocallyConstant f) :
    ∃ y, f = Function.const X y := by
  cases is_empty_or_nonempty X
  · exact ⟨Classical.arbitrary Y, funext <| h.elim⟩
    
  · exact ⟨f (Classical.arbitrary X), hf.eq_const _⟩
    

theorem iff_is_const [PreconnectedSpace X] {f : X → Y} : IsLocallyConstant f ↔ ∀ x y, f x = f y :=
  ⟨fun h x y => h.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial, of_constant _⟩

theorem range_finite [CompactSpace X] {f : X → Y} (hf : IsLocallyConstant f) : (Set.Range f).Finite := by
  letI : TopologicalSpace Y := ⊥
  haveI : DiscreteTopology Y := ⟨rfl⟩
  rw [@iff_continuous X Y ‹_› ‹_›] at hf
  exact (is_compact_range hf).finite_of_discrete

@[to_additive]
theorem one [One Y] : IsLocallyConstant (1 : X → Y) :=
  const 1

@[to_additive]
theorem inv [Inv Y] ⦃f : X → Y⦄ (hf : IsLocallyConstant f) : IsLocallyConstant f⁻¹ :=
  hf.comp fun x => x⁻¹

@[to_additive]
theorem mul [Mul Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f * g) :=
  hf.comp₂ hg (· * ·)

@[to_additive]
theorem div [Div Y] ⦃f g : X → Y⦄ (hf : IsLocallyConstant f) (hg : IsLocallyConstant g) : IsLocallyConstant (f / g) :=
  hf.comp₂ hg (· / ·)

/-- If a composition of a function `f` followed by an injection `g` is locally
constant, then the locally constant property descends to `f`. -/
theorem desc {α β : Type _} (f : X → α) (g : α → β) (h : IsLocallyConstant (g ∘ f)) (inj : Function.Injective g) :
    IsLocallyConstant f := by
  rw [(IsLocallyConstant.tfae f).out 0 3]
  intro a
  have : f ⁻¹' {a} = g ∘ f ⁻¹' {g a} := by
    ext x
    simp only [mem_singleton_iff, Function.comp_app, mem_preimage]
    exact ⟨fun h => by rw [h], fun h => inj h⟩
  rw [this]
  apply h

theorem of_constant_on_connected_components [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ x, ∀ y ∈ ConnectedComponent x, f y = f x) : IsLocallyConstant f := by
  rw [iff_exists_open]
  exact fun x => ⟨ConnectedComponent x, is_open_connected_component, mem_connected_component, h x⟩

theorem of_constant_on_preconnected_clopens [LocallyConnectedSpace X] {f : X → Y}
    (h : ∀ U : Set X, IsPreconnected U → IsClopen U → ∀ x ∈ U, ∀ y ∈ U, f y = f x) : IsLocallyConstant f :=
  of_constant_on_connected_components fun x =>
    h (ConnectedComponent x) is_preconnected_connected_component is_clopen_connected_component x mem_connected_component

end IsLocallyConstant

/-- A (bundled) locally constant function from a topological space `X` to a type `Y`. -/
structure LocallyConstant (X Y : Type _) [TopologicalSpace X] where
  toFun : X → Y
  IsLocallyConstant : IsLocallyConstant to_fun

namespace LocallyConstant

instance [Inhabited Y] : Inhabited (LocallyConstant X Y) :=
  ⟨⟨_, IsLocallyConstant.const default⟩⟩

instance : CoeFun (LocallyConstant X Y) fun _ => X → Y :=
  ⟨LocallyConstant.toFun⟩

initialize_simps_projections LocallyConstant (toFun → apply)

@[simp]
theorem to_fun_eq_coe (f : LocallyConstant X Y) : f.toFun = f :=
  rfl

@[simp]
theorem coe_mk (f : X → Y) (h) : ⇑(⟨f, h⟩ : LocallyConstant X Y) = f :=
  rfl

theorem congr_fun {f g : LocallyConstant X Y} (h : f = g) (x : X) : f x = g x :=
  congr_arg (fun h : LocallyConstant X Y => h x) h

theorem congr_arg (f : LocallyConstant X Y) {x y : X} (h : x = y) : f x = f y :=
  congr_arg (fun x : X => f x) h

theorem coe_injective : @Function.Injective (LocallyConstant X Y) (X → Y) coeFn
  | ⟨f, hf⟩, ⟨g, hg⟩, h => by
    have : f = g := h
    subst f

@[simp, norm_cast]
theorem coe_inj {f g : LocallyConstant X Y} : (f : X → Y) = g ↔ f = g :=
  coe_injective.eq_iff

@[ext]
theorem ext ⦃f g : LocallyConstant X Y⦄ (h : ∀ x, f x = g x) : f = g :=
  coe_injective (funext h)

theorem ext_iff {f g : LocallyConstant X Y} : f = g ↔ ∀ x, f x = g x :=
  ⟨fun h x => h ▸ rfl, fun h => ext h⟩

section CodomainTopologicalSpace

variable [TopologicalSpace Y] (f : LocallyConstant X Y)

protected theorem continuous : Continuous f :=
  f.IsLocallyConstant.Continuous

/-- We can turn a locally-constant function into a bundled `continuous_map`. -/
def toContinuousMap : C(X, Y) :=
  ⟨f, f.Continuous⟩

/-- As a shorthand, `locally_constant.to_continuous_map` is available as a coercion -/
instance : Coe (LocallyConstant X Y) C(X, Y) :=
  ⟨toContinuousMap⟩

@[simp]
theorem to_continuous_map_eq_coe : f.toContinuousMap = f :=
  rfl

@[simp]
theorem coe_continuous_map : ((f : C(X, Y)) : X → Y) = (f : X → Y) :=
  rfl

theorem to_continuous_map_injective : Function.Injective (toContinuousMap : LocallyConstant X Y → C(X, Y)) :=
  fun _ _ h => ext (ContinuousMap.congr_fun h)

end CodomainTopologicalSpace

/-- The constant locally constant function on `X` with value `y : Y`. -/
def const (X : Type _) {Y : Type _} [TopologicalSpace X] (y : Y) : LocallyConstant X Y :=
  ⟨Function.const X y, IsLocallyConstant.const _⟩

@[simp]
theorem coe_const (y : Y) : (const X y : X → Y) = Function.const X y :=
  rfl

/- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:31:4: unsupported: too many args: fin_cases ... #[[]] -/
/-- The locally constant function to `fin 2` associated to a clopen set. -/
def ofClopen {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
    LocallyConstant X (Fin 2) where
  toFun x := if x ∈ U then 0 else 1
  IsLocallyConstant := by
    rw [(IsLocallyConstant.tfae fun x => if x ∈ U then (0 : Fin 2) else 1).out 0 3]
    intro e
    fin_cases e
    · convert hU.1 using 1
      ext
      simp only [Nat.one_ne_zero, mem_singleton_iff, Fin.one_eq_zero_iff, mem_preimage, ite_eq_left_iff]
      tauto
      
    · rw [← is_closed_compl_iff]
      convert hU.2
      ext
      simp
      

@[simp]
theorem of_clopen_fiber_zero {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
    ofClopen hU ⁻¹' ({0} : Set (Fin 2)) = U := by
  ext
  simp only [of_clopen, Nat.one_ne_zero, mem_singleton_iff, Fin.one_eq_zero_iff, coe_mk, mem_preimage, ite_eq_left_iff]
  tauto

@[simp]
theorem of_clopen_fiber_one {X : Type _} [TopologicalSpace X] {U : Set X} [∀ x, Decidable (x ∈ U)] (hU : IsClopen U) :
    ofClopen hU ⁻¹' ({1} : Set (Fin 2)) = Uᶜ := by
  ext
  simp only [of_clopen, Nat.one_ne_zero, mem_singleton_iff, coe_mk, Fin.zero_eq_one_iff, mem_preimage, ite_eq_right_iff,
    mem_compl_iff]
  tauto

theorem locally_constant_eq_of_fiber_zero_eq {X : Type _} [TopologicalSpace X] (f g : LocallyConstant X (Fin 2))
    (h : f ⁻¹' ({0} : Set (Fin 2)) = g ⁻¹' {0}) : f = g := by
  simp only [Set.ext_iff, mem_singleton_iff, mem_preimage] at h
  ext1 x
  exact Fin.fin_two_eq_of_eq_zero_iff (h x)

theorem range_finite [CompactSpace X] (f : LocallyConstant X Y) : (Set.Range f).Finite :=
  f.IsLocallyConstant.range_finite

theorem apply_eq_of_is_preconnected (f : LocallyConstant X Y) {s : Set X} (hs : IsPreconnected s) {x y : X} (hx : x ∈ s)
    (hy : y ∈ s) : f x = f y :=
  f.IsLocallyConstant.apply_eq_of_is_preconnected hs hx hy

theorem apply_eq_of_preconnected_space [PreconnectedSpace X] (f : LocallyConstant X Y) (x y : X) : f x = f y :=
  f.IsLocallyConstant.apply_eq_of_is_preconnected is_preconnected_univ trivial trivial

theorem eq_const [PreconnectedSpace X] (f : LocallyConstant X Y) (x : X) : f = const X (f x) :=
  ext fun y => apply_eq_of_preconnected_space f _ _

theorem exists_eq_const [PreconnectedSpace X] [Nonempty Y] (f : LocallyConstant X Y) : ∃ y, f = const X y := by
  rcases Classical.em (Nonempty X) with (⟨⟨x⟩⟩ | hX)
  · exact ⟨f x, f.eq_const x⟩
    
  · exact ⟨Classical.arbitrary Y, ext fun x => (hX ⟨x⟩).elim⟩
    

/-- Push forward of locally constant maps under any map, by post-composition. -/
def map (f : Y → Z) : LocallyConstant X Y → LocallyConstant X Z := fun g =>
  ⟨f ∘ g, fun s => by
    rw [Set.preimage_comp]
    apply g.is_locally_constant⟩

@[simp]
theorem map_apply (f : Y → Z) (g : LocallyConstant X Y) : ⇑(map f g) = f ∘ g :=
  rfl

@[simp]
theorem map_id : @map X Y Y _ id = id := by
  ext
  rfl

@[simp]
theorem map_comp {Y₁ Y₂ Y₃ : Type _} (g : Y₂ → Y₃) (f : Y₁ → Y₂) : @map X _ _ _ g ∘ map f = map (g ∘ f) := by
  ext
  rfl

/-- Given a locally constant function to `α → β`, construct a family of locally constant
functions with values in β indexed by α. -/
def flip {X α β : Type _} [TopologicalSpace X] (f : LocallyConstant X (α → β)) (a : α) : LocallyConstant X β :=
  f.map fun f => f a

/-- If α is finite, this constructs a locally constant function to `α → β` given a
family of locally constant functions with values in β indexed by α. -/
def unflip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
    LocallyConstant X (α → β) where
  toFun x a := f a x
  IsLocallyConstant := by
    rw [(IsLocallyConstant.tfae fun x a => f a x).out 0 3]
    intro g
    have : (fun (x : X) (a : α) => f a x) ⁻¹' {g} = ⋂ a : α, f a ⁻¹' {g a} := by tidy
    rw [this]
    apply is_open_Inter
    intro a
    apply (f a).IsLocallyConstant

@[simp]
theorem unflip_flip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : LocallyConstant X (α → β)) :
    unflip f.flip = f := by
  ext
  rfl

@[simp]
theorem flip_unflip {X α β : Type _} [Fintype α] [TopologicalSpace X] (f : α → LocallyConstant X β) :
    (unflip f).flip = f := by
  ext
  rfl

section Comap

open Classical

variable [TopologicalSpace Y]

/-- Pull back of locally constant maps under any map, by pre-composition.

This definition only makes sense if `f` is continuous,
in which case it sends locally constant functions to their precomposition with `f`.
See also `locally_constant.coe_comap`. -/
noncomputable def comap (f : X → Y) : LocallyConstant Y Z → LocallyConstant X Z :=
  if hf : Continuous f then fun g => ⟨g ∘ f, g.IsLocallyConstant.comp_continuous hf⟩
  else by
    by_cases H:Nonempty X
    · intro g
      exact const X (g <| f <| Classical.arbitrary X)
      
    · intro g
      refine' ⟨fun x => (H ⟨x⟩).elim, _⟩
      intro s
      rw [is_open_iff_nhds]
      intro x
      exact (H ⟨x⟩).elim
      

@[simp]
theorem coe_comap (f : X → Y) (g : LocallyConstant Y Z) (hf : Continuous f) : ⇑(comap f g) = g ∘ f := by
  rw [comap, dif_pos hf]
  rfl

@[simp]
theorem comap_id : @comap X X Z _ _ id = id := by
  ext
  simp only [continuous_id, id.def, Function.comp.right_id, coe_comap]

theorem comap_comp [TopologicalSpace Z] (f : X → Y) (g : Y → Z) (hf : Continuous f) (hg : Continuous g) :
    @comap _ _ α _ _ f ∘ comap g = comap (g ∘ f) := by
  ext
  simp only [hf, hg, hg.comp hf, coe_comap]

theorem comap_const (f : X → Y) (y : Y) (h : ∀ x, f x = y) :
    (comap f : LocallyConstant Y Z → LocallyConstant X Z) = fun g => ⟨fun x => g y, IsLocallyConstant.const _⟩ := by
  ext
  rw [coe_comap]
  · simp only [h, coe_mk, Function.comp_app]
    
  · rw [show f = fun x => y by ext <;> apply h]
    exact continuous_const
    

end Comap

section Desc

/-- If a locally constant function factors through an injection, then it factors through a locally
constant function. -/
def desc {X α β : Type _} [TopologicalSpace X] {g : α → β} (f : X → α) (h : LocallyConstant X β) (cond : g ∘ f = h)
    (inj : Function.Injective g) : LocallyConstant X α where
  toFun := f
  IsLocallyConstant :=
    IsLocallyConstant.desc _ g
      (by
        rw [cond]
        exact h.2)
      inj

@[simp]
theorem coe_desc {X α β : Type _} [TopologicalSpace X] (f : X → α) (g : α → β) (h : LocallyConstant X β)
    (cond : g ∘ f = h) (inj : Function.Injective g) : ⇑(desc f h cond inj) = f :=
  rfl

end Desc

section Indicator

variable {R : Type _} [One R] {U : Set X} (f : LocallyConstant X R)

open Classical

/-- Given a clopen set `U` and a locally constant function `f`, `locally_constant.mul_indicator`
  returns the locally constant function that is `f` on `U` and `1` otherwise. -/
@[to_additive
      " Given a clopen set `U` and a locally constant function `f`,\n  `locally_constant.indicator` returns the locally constant function that is `f` on `U` and `0`\n  otherwise. ",
  simps]
noncomputable def mulIndicator (hU : IsClopen U) : LocallyConstant X R where
  toFun := Set.mulIndicator U f
  IsLocallyConstant := by
    rw [IsLocallyConstant.iff_exists_open]
    rintro x
    obtain ⟨V, hV, hx, h'⟩ := (IsLocallyConstant.iff_exists_open _).1 f.is_locally_constant x
    by_cases x ∈ U
    · refine' ⟨U ∩ V, IsOpen.inter hU.1 hV, Set.mem_inter h hx, _⟩
      rintro y hy
      rw [Set.mem_inter_iff] at hy
      rw [Set.mul_indicator_of_mem hy.1, Set.mul_indicator_of_mem h]
      apply h' y hy.2
      
    · rw [← Set.mem_compl_iff] at h
      refine' ⟨Uᶜ, (IsClopen.compl hU).1, h, _⟩
      rintro y hy
      rw [Set.mem_compl_iff] at h
      rw [Set.mem_compl_iff] at hy
      simp [h, hy]
      

variable (a : X)

@[to_additive]
theorem mul_indicator_apply_eq_if (hU : IsClopen U) : mulIndicator f hU a = if a ∈ U then f a else 1 :=
  Set.mul_indicator_apply U f a

variable {a}

@[to_additive]
theorem mul_indicator_of_mem (hU : IsClopen U) (h : a ∈ U) : f.mulIndicator hU a = f a := by
  rw [mul_indicator_apply]
  apply Set.mul_indicator_of_mem h

@[to_additive]
theorem mul_indicator_of_not_mem (hU : IsClopen U) (h : a ∉ U) : f.mulIndicator hU a = 1 := by
  rw [mul_indicator_apply]
  apply Set.mul_indicator_of_not_mem h

end Indicator

end LocallyConstant

