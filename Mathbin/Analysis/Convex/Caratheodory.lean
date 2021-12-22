import Mathbin.Analysis.Convex.Combination
import Mathbin.LinearAlgebra.AffineSpace.Independent
import Mathbin.Tactic.FieldSimp

/-!
# Carathéodory's convexity theorem

Convex hull can be regarded as a refinement of affine span. Both are closure operators but whereas
convex hull takes values in the lattice of convex subsets, affine span takes values in the much
coarser sublattice of affine subspaces.

The cost of this refinement is that one no longer has bases. However Carathéodory's convexity
theorem offers some compensation. Given a set `s` together with a point `x` in its convex hull,
Carathéodory says that one may find an affine-independent family of elements `s` whose convex hull
contains `x`. Thus the difference from the case of affine span is that the affine-independent family
depends on `x`.

In particular, in finite dimensions Carathéodory's theorem implies that the convex hull of a set `s`
in `𝕜ᵈ` is the union of the convex hulls of the `(d + 1)`-tuples in `s`.

## Main results

* `convex_hull_eq_union`: Carathéodory's convexity theorem

## Implementation details

This theorem was formalized as part of the Sphere Eversion project.

## Tags
convex hull, caratheodory

-/


open Set Finset

open_locale BigOperators

universe u

variable {𝕜 : Type _} {E : Type u} [LinearOrderedField 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]

namespace Caratheodory

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If `x` is in the convex hull of some finset `t` whose elements are not affine-independent,\nthen it is in the convex hull of a strict subset of `t`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `mem_convex_hull_erase [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `DecidableEq [`E]) "]")
    (Term.implicitBinder "{" [`t] [":" (Term.app `Finset [`E])] "}")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term¬_»
       "¬"
       (Term.app
        `AffineIndependent
        [`𝕜 (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t "→" `E))]] ")")]))]
     []
     ")")
    (Term.implicitBinder "{" [`x] [":" `E] "}")
    (Term.explicitBinder
     "("
     [`m]
     [":"
      (Init.Core.«term_∈_»
       `x
       " ∈ "
       (Term.app
        `convexHull
        [`𝕜 (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `y)]
       [":" (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))
     ","
     (Init.Core.«term_∈_»
      `x
      " ∈ "
      (Term.app
       `convexHull
       [`𝕜
        (Term.paren
         "("
         [(Init.Coe.«term↑_» "↑" (Term.app `t.erase [`y])) [(Term.typeAscription ":" (Term.app `Set [`E]))]]
         ")")])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `Finset.convex_hull_eq) "," (Tactic.simpLemma [] [] `mem_set_of_eq)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`m] ["⊢"]))])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `fpos)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `fsum)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
             "⟩")])]
         []
         [":=" [`m]])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `g)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gcombo)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gsum)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gpos)]) [])]
             "⟩")])]
         []
         [":=" [(Term.app `exists_nontrivial_relation_sum_zero_of_not_affine_ind [`h])]])
        [])
       (group
        (Tactic.replace
         "replace"
         (Term.haveDecl
          (Term.haveIdDecl [`gpos []] [] ":=" (Term.app `exists_pos_of_sum_zero_of_exists_nonzero [`g `gsum `gpos]))))
        [])
       (group (Tactic.clear "clear" [`h]) [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `s
           []
           ":="
           (Term.app
            `t.filter
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`z] [(Term.typeSpec ":" `E)])]
               "=>"
               («term_<_» (numLit "0") "<" (Term.app `g [`z]))))]))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₀)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `mem)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])]
             "⟩")])]
         [":"
          (Mathlib.ExtendedBinder.«term∃___,_»
           "∃"
           `i₀
           («binderTerm∈_» "∈" `s)
           ","
           (Term.forall
            "∀"
            []
            ","
            (Mathlib.ExtendedBinder.«term∀___,_»
             "∀"
             `i
             («binderTerm∈_» "∈" `s)
             ","
             (Term.forall
              "∀"
              []
              ","
              («term_≤_»
               («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
               "≤"
               («term_/_» (Term.app `f [`i]) "/" (Term.app `g [`i])))))))]
         [])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.apply
              "apply"
              (Term.app
               `s.exists_min_image
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`z] [])]
                  "=>"
                  («term_/_» (Term.app `f [`z]) "/" (Term.app `g [`z]))))]))
             [])
            (group
             (Tactic.obtain
              "obtain"
              [(Tactic.rcasesPatMed
                [(Tactic.rcasesPat.tuple
                  "⟨"
                  [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
                   ","
                   (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hgx)]) [])]
                  "⟩")])]
              [":"
               (Mathlib.ExtendedBinder.«term∃___,_»
                "∃"
                `x
                («binderTerm∈_» "∈" `t)
                ","
                («term_<_» (numLit "0") "<" (Term.app `g [`x])))]
              [":=" [`gpos]])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`x "," (Term.app `mem_filter.mpr [(Term.anonymousCtor "⟨" [`hx "," `hgx] "⟩")])]
               "⟩"))
             [])])))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hg []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `g [`i₀])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_filter)] "]")
                 [(Tactic.location "at" (Tactic.locationHyp [`mem] []))])
                [])
               (group (Tactic.exact "exact" (Term.proj `mem "." (fieldIdx "2"))) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hi₀ []]
           [(Term.typeSpec ":" (Init.Core.«term_∈_» `i₀ " ∈ " `t))]
           ":="
           (Term.app `filter_subset [(Term.hole "_") (Term.hole "_") `mem]))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `k
           [(Term.typeSpec ":" (Term.arrow `E "→" `𝕜))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`z] [])]
             "=>"
             («term_-_»
              (Term.app `f [`z])
              "-"
              (Finset.Data.Finset.Fold.«term_*_»
               («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
               "*"
               (Term.app `g [`z]))))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`hk []]
           [(Term.typeSpec ":" («term_=_» (Term.app `k [`i₀]) "=" (numLit "0")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.fieldSimp
                 "field_simp"
                 []
                 []
                 ["[" [(Tactic.simpLemma [] [] `k) "," (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hg]))] "]"]
                 []
                 [])
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`ksum []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
               " in "
               (Term.app `t.erase [`i₀])
               ", "
               (Term.app `k [`e]))
              "="
              (numLit "1")))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (tacticCalc_
                 "calc"
                 [(calcStep
                   («term_=_»
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                     " in "
                     (Term.app `t.erase [`i₀])
                     ", "
                     (Term.app `k [`e]))
                    "="
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                     " in "
                     `t
                     ", "
                     (Term.app `k [`e])))
                   ":="
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group
                        (Mathlib.Tactic.Conv.convRHS
                         "conv_rhs"
                         []
                         []
                         "=>"
                         (Tactic.Conv.convSeq
                          (Tactic.Conv.convSeq1Indented
                           [(group
                             (Tactic.Conv.convRw__
                              "rw"
                              []
                              (Tactic.rwRuleSeq
                               "["
                               [(Tactic.rwRule ["←"] (Term.app `insert_erase [`hi₀]))
                                ","
                                (Tactic.rwRule [] (Term.app `sum_insert [(Term.app `not_mem_erase [`i₀ `t])]))
                                ","
                                (Tactic.rwRule [] `hk)
                                ","
                                (Tactic.rwRule [] `zero_addₓ)]
                               "]"))
                             [])])))
                        [])]))))
                  (calcStep
                   («term_=_»
                    (Term.hole "_")
                    "="
                    (Algebra.BigOperators.Basic.«term∑_in_,_»
                     "∑"
                     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                     " in "
                     `t
                     ", "
                     («term_-_»
                      (Term.app `f [`e])
                      "-"
                      (Finset.Data.Finset.Fold.«term_*_»
                       («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
                       "*"
                       (Term.app `g [`e])))))
                   ":="
                   `rfl)
                  (calcStep
                   («term_=_» (Term.hole "_") "=" (numLit "1"))
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
                          [(Tactic.rwRule [] `sum_sub_distrib)
                           ","
                           (Tactic.rwRule [] `fsum)
                           ","
                           (Tactic.rwRule ["←"] `mul_sum)
                           ","
                           (Tactic.rwRule [] `gsum)
                           ","
                           (Tactic.rwRule [] `mul_zero)
                           ","
                           (Tactic.rwRule [] `sub_zero)]
                          "]")
                         [])
                        [])]))))])
                [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [(Term.anonymousCtor "⟨" [`i₀ "," `hi₀] "⟩") "," `k "," (Term.hole "_") "," `ksum "," (Term.hole "_")]
          "⟩"))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `and_imp)
                ","
                (Tactic.simpLemma [] [] `sub_nonneg)
                ","
                (Tactic.simpLemma [] [] `mem_erase)
                ","
                (Tactic.simpLemma [] [] `Ne.def)
                ","
                (Tactic.simpLemma [] [] `Subtype.coe_mk)]
               "]"]
              [])
             [])
            (group (Tactic.intro "intro" [`e `hei₀ `het]) [])
            (group (Tactic.byCases' "by_cases'" [`hes ":"] (Init.Core.«term_∈_» `e " ∈ " `s)) [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.tacticHave_
                   "have"
                   (Term.haveDecl
                    (Term.haveIdDecl
                     [`hge []]
                     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `g [`e])))]
                     ":="
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_filter)] "]")
                           [(Tactic.location "at" (Tactic.locationHyp [`hes] []))])
                          [])
                         (group (Tactic.exact "exact" (Term.proj `hes "." (fieldIdx "2"))) [])]))))))
                  [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `le_div_iff [`hge]))] "]")
                   [])
                  [])
                 (group (Tactic.exact "exact" (Term.app `w [(Term.hole "_") `hes])) [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (tacticCalc_
                   "calc"
                   [(calcStep
                     («term_≤_» (Term.hole "_") "≤" (numLit "0"))
                     ":="
                     (Term.app `mul_nonpos_of_nonneg_of_nonpos [(Term.hole "_") (Term.hole "_")]))
                    (calcStep («term_≤_» (Term.hole "_") "≤" (Term.app `f [`e])) ":=" (Term.app `fpos [`e `het]))])
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.apply
                        "apply"
                        (Term.app
                         `div_nonneg
                         [(Term.app
                           `fpos
                           [`i₀ (Term.app `mem_of_subset [(Term.app `filter_subset [(Term.hole "_") `t]) `mem])])
                          (Term.app `le_of_ltₓ [`hg])]))
                       [])])))
                  [])
                 (group
                  (Tactic.«tactic·._»
                   "·"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.simpa
                        "simpa"
                        []
                        ["only"]
                        ["["
                         [(Tactic.simpLemma [] [] `mem_filter)
                          ","
                          (Tactic.simpLemma [] [] `het)
                          ","
                          (Tactic.simpLemma [] [] `true_andₓ)
                          ","
                          (Tactic.simpLemma [] [] `not_ltₓ)]
                         "]"]
                        []
                        ["using" `hes])
                       [])])))
                  [])])))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Subtype.coe_mk)
                ","
                (Tactic.simpLemma [] [] (Term.app `center_mass_eq_of_sum_1 [(Term.hole "_") `id `ksum]))
                ","
                (Tactic.simpLemma [] [] `id)]
               "]"]
              [])
             [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_=_»
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                  " in "
                  (Term.app `t.erase [`i₀])
                  ", "
                  (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e))
                 "="
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                  " in "
                  `t
                  ", "
                  (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e)))
                ":="
                (Term.app
                 `sum_erase
                 [(Term.hole "_")
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk) "," (Tactic.rwRule [] `zero_smul)] "]")
                        [])
                       [])])))]))
               (calcStep
                («term_=_»
                 (Term.hole "_")
                 "="
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                  " in "
                  `t
                  ", "
                  (Algebra.Group.Defs.«term_•_»
                   («term_-_»
                    (Term.app `f [`e])
                    "-"
                    (Finset.Data.Finset.Fold.«term_*_»
                     («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
                     "*"
                     (Term.app `g [`e])))
                   " • "
                   `e)))
                ":="
                `rfl)
               (calcStep («term_=_» (Term.hole "_") "=" (Term.app `t.center_mass [`f `id])) ":=" (Term.hole "_"))])
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `sub_smul)
                ","
                (Tactic.simpLemma [] [] `mul_smul)
                ","
                (Tactic.simpLemma [] [] `sum_sub_distrib)
                ","
                (Tactic.simpLemma [] ["←"] `smul_sum)
                ","
                (Tactic.simpLemma [] [] `gcombo)
                ","
                (Tactic.simpLemma [] [] `smul_zero)
                ","
                (Tactic.simpLemma [] [] `sub_zero)
                ","
                (Tactic.simpLemma [] [] `center_mass)
                ","
                (Tactic.simpLemma [] [] `fsum)
                ","
                (Tactic.simpLemma [] [] `inv_one)
                ","
                (Tactic.simpLemma [] [] `one_smul)
                ","
                (Tactic.simpLemma [] [] `id.def)]
               "]"]
              [])
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
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Finset.convex_hull_eq) "," (Tactic.simpLemma [] [] `mem_set_of_eq)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`m] ["⊢"]))])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `f)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `fpos)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `fsum)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rfl)]) [])]
            "⟩")])]
        []
        [":=" [`m]])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `g)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gcombo)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gsum)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `gpos)]) [])]
            "⟩")])]
        []
        [":=" [(Term.app `exists_nontrivial_relation_sum_zero_of_not_affine_ind [`h])]])
       [])
      (group
       (Tactic.replace
        "replace"
        (Term.haveDecl
         (Term.haveIdDecl [`gpos []] [] ":=" (Term.app `exists_pos_of_sum_zero_of_exists_nonzero [`g `gsum `gpos]))))
       [])
      (group (Tactic.clear "clear" [`h]) [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `s
          []
          ":="
          (Term.app
           `t.filter
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`z] [(Term.typeSpec ":" `E)])]
              "=>"
              («term_<_» (numLit "0") "<" (Term.app `g [`z]))))]))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `i₀)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `mem)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])]
            "⟩")])]
        [":"
         (Mathlib.ExtendedBinder.«term∃___,_»
          "∃"
          `i₀
          («binderTerm∈_» "∈" `s)
          ","
          (Term.forall
           "∀"
           []
           ","
           (Mathlib.ExtendedBinder.«term∀___,_»
            "∀"
            `i
            («binderTerm∈_» "∈" `s)
            ","
            (Term.forall
             "∀"
             []
             ","
             («term_≤_»
              («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
              "≤"
              («term_/_» (Term.app `f [`i]) "/" (Term.app `g [`i])))))))]
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.apply
             "apply"
             (Term.app
              `s.exists_min_image
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`z] [])]
                 "=>"
                 («term_/_» (Term.app `f [`z]) "/" (Term.app `g [`z]))))]))
            [])
           (group
            (Tactic.obtain
             "obtain"
             [(Tactic.rcasesPatMed
               [(Tactic.rcasesPat.tuple
                 "⟨"
                 [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `x)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hx)]) [])
                  ","
                  (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hgx)]) [])]
                 "⟩")])]
             [":"
              (Mathlib.ExtendedBinder.«term∃___,_»
               "∃"
               `x
               («binderTerm∈_» "∈" `t)
               ","
               («term_<_» (numLit "0") "<" (Term.app `g [`x])))]
             [":=" [`gpos]])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`x "," (Term.app `mem_filter.mpr [(Term.anonymousCtor "⟨" [`hx "," `hgx] "⟩")])]
              "⟩"))
            [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hg []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `g [`i₀])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_filter)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`mem] []))])
               [])
              (group (Tactic.exact "exact" (Term.proj `mem "." (fieldIdx "2"))) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hi₀ []]
          [(Term.typeSpec ":" (Init.Core.«term_∈_» `i₀ " ∈ " `t))]
          ":="
          (Term.app `filter_subset [(Term.hole "_") (Term.hole "_") `mem]))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `k
          [(Term.typeSpec ":" (Term.arrow `E "→" `𝕜))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`z] [])]
            "=>"
            («term_-_»
             (Term.app `f [`z])
             "-"
             (Finset.Data.Finset.Fold.«term_*_»
              («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
              "*"
              (Term.app `g [`z]))))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`hk []]
          [(Term.typeSpec ":" («term_=_» (Term.app `k [`i₀]) "=" (numLit "0")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.fieldSimp
                "field_simp"
                []
                []
                ["[" [(Tactic.simpLemma [] [] `k) "," (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hg]))] "]"]
                []
                [])
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`ksum []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
              " in "
              (Term.app `t.erase [`i₀])
              ", "
              (Term.app `k [`e]))
             "="
             (numLit "1")))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (tacticCalc_
                "calc"
                [(calcStep
                  («term_=_»
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                    " in "
                    (Term.app `t.erase [`i₀])
                    ", "
                    (Term.app `k [`e]))
                   "="
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                    " in "
                    `t
                    ", "
                    (Term.app `k [`e])))
                  ":="
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group
                       (Mathlib.Tactic.Conv.convRHS
                        "conv_rhs"
                        []
                        []
                        "=>"
                        (Tactic.Conv.convSeq
                         (Tactic.Conv.convSeq1Indented
                          [(group
                            (Tactic.Conv.convRw__
                             "rw"
                             []
                             (Tactic.rwRuleSeq
                              "["
                              [(Tactic.rwRule ["←"] (Term.app `insert_erase [`hi₀]))
                               ","
                               (Tactic.rwRule [] (Term.app `sum_insert [(Term.app `not_mem_erase [`i₀ `t])]))
                               ","
                               (Tactic.rwRule [] `hk)
                               ","
                               (Tactic.rwRule [] `zero_addₓ)]
                              "]"))
                            [])])))
                       [])]))))
                 (calcStep
                  («term_=_»
                   (Term.hole "_")
                   "="
                   (Algebra.BigOperators.Basic.«term∑_in_,_»
                    "∑"
                    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                    " in "
                    `t
                    ", "
                    («term_-_»
                     (Term.app `f [`e])
                     "-"
                     (Finset.Data.Finset.Fold.«term_*_»
                      («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
                      "*"
                      (Term.app `g [`e])))))
                  ":="
                  `rfl)
                 (calcStep
                  («term_=_» (Term.hole "_") "=" (numLit "1"))
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
                         [(Tactic.rwRule [] `sum_sub_distrib)
                          ","
                          (Tactic.rwRule [] `fsum)
                          ","
                          (Tactic.rwRule ["←"] `mul_sum)
                          ","
                          (Tactic.rwRule [] `gsum)
                          ","
                          (Tactic.rwRule [] `mul_zero)
                          ","
                          (Tactic.rwRule [] `sub_zero)]
                         "]")
                        [])
                       [])]))))])
               [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [(Term.anonymousCtor "⟨" [`i₀ "," `hi₀] "⟩") "," `k "," (Term.hole "_") "," `ksum "," (Term.hole "_")]
         "⟩"))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `and_imp)
               ","
               (Tactic.simpLemma [] [] `sub_nonneg)
               ","
               (Tactic.simpLemma [] [] `mem_erase)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_mk)]
              "]"]
             [])
            [])
           (group (Tactic.intro "intro" [`e `hei₀ `het]) [])
           (group (Tactic.byCases' "by_cases'" [`hes ":"] (Init.Core.«term_∈_» `e " ∈ " `s)) [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.tacticHave_
                  "have"
                  (Term.haveDecl
                   (Term.haveIdDecl
                    [`hge []]
                    [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.app `g [`e])))]
                    ":="
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mem_filter)] "]")
                          [(Tactic.location "at" (Tactic.locationHyp [`hes] []))])
                         [])
                        (group (Tactic.exact "exact" (Term.proj `hes "." (fieldIdx "2"))) [])]))))))
                 [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `le_div_iff [`hge]))] "]")
                  [])
                 [])
                (group (Tactic.exact "exact" (Term.app `w [(Term.hole "_") `hes])) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (tacticCalc_
                  "calc"
                  [(calcStep
                    («term_≤_» (Term.hole "_") "≤" (numLit "0"))
                    ":="
                    (Term.app `mul_nonpos_of_nonneg_of_nonpos [(Term.hole "_") (Term.hole "_")]))
                   (calcStep («term_≤_» (Term.hole "_") "≤" (Term.app `f [`e])) ":=" (Term.app `fpos [`e `het]))])
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.apply
                       "apply"
                       (Term.app
                        `div_nonneg
                        [(Term.app
                          `fpos
                          [`i₀ (Term.app `mem_of_subset [(Term.app `filter_subset [(Term.hole "_") `t]) `mem])])
                         (Term.app `le_of_ltₓ [`hg])]))
                      [])])))
                 [])
                (group
                 (Tactic.«tactic·._»
                  "·"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.simpa
                       "simpa"
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `mem_filter)
                         ","
                         (Tactic.simpLemma [] [] `het)
                         ","
                         (Tactic.simpLemma [] [] `true_andₓ)
                         ","
                         (Tactic.simpLemma [] [] `not_ltₓ)]
                        "]"]
                       []
                       ["using" `hes])
                      [])])))
                 [])])))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Subtype.coe_mk)
               ","
               (Tactic.simpLemma [] [] (Term.app `center_mass_eq_of_sum_1 [(Term.hole "_") `id `ksum]))
               ","
               (Tactic.simpLemma [] [] `id)]
              "]"]
             [])
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_=_»
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                 " in "
                 (Term.app `t.erase [`i₀])
                 ", "
                 (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e))
                "="
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                 " in "
                 `t
                 ", "
                 (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e)))
               ":="
               (Term.app
                `sum_erase
                [(Term.hole "_")
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk) "," (Tactic.rwRule [] `zero_smul)] "]")
                       [])
                      [])])))]))
              (calcStep
               («term_=_»
                (Term.hole "_")
                "="
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
                 " in "
                 `t
                 ", "
                 (Algebra.Group.Defs.«term_•_»
                  («term_-_»
                   (Term.app `f [`e])
                   "-"
                   (Finset.Data.Finset.Fold.«term_*_»
                    («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
                    "*"
                    (Term.app `g [`e])))
                  " • "
                  `e)))
               ":="
               `rfl)
              (calcStep («term_=_» (Term.hole "_") "=" (Term.app `t.center_mass [`f `id])) ":=" (Term.hole "_"))])
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `sub_smul)
               ","
               (Tactic.simpLemma [] [] `mul_smul)
               ","
               (Tactic.simpLemma [] [] `sum_sub_distrib)
               ","
               (Tactic.simpLemma [] ["←"] `smul_sum)
               ","
               (Tactic.simpLemma [] [] `gcombo)
               ","
               (Tactic.simpLemma [] [] `smul_zero)
               ","
               (Tactic.simpLemma [] [] `sub_zero)
               ","
               (Tactic.simpLemma [] [] `center_mass)
               ","
               (Tactic.simpLemma [] [] `fsum)
               ","
               (Tactic.simpLemma [] [] `inv_one)
               ","
               (Tactic.simpLemma [] [] `one_smul)
               ","
               (Tactic.simpLemma [] [] `id.def)]
              "]"]
             [])
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
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `Subtype.coe_mk)
          ","
          (Tactic.simpLemma [] [] (Term.app `center_mass_eq_of_sum_1 [(Term.hole "_") `id `ksum]))
          ","
          (Tactic.simpLemma [] [] `id)]
         "]"]
        [])
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
            " in "
            (Term.app `t.erase [`i₀])
            ", "
            (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e))
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
            " in "
            `t
            ", "
            (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e)))
          ":="
          (Term.app
           `sum_erase
           [(Term.hole "_")
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk) "," (Tactic.rwRule [] `zero_smul)] "]")
                  [])
                 [])])))]))
         (calcStep
          («term_=_»
           (Term.hole "_")
           "="
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
            " in "
            `t
            ", "
            (Algebra.Group.Defs.«term_•_»
             («term_-_»
              (Term.app `f [`e])
              "-"
              (Finset.Data.Finset.Fold.«term_*_»
               («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
               "*"
               (Term.app `g [`e])))
             " • "
             `e)))
          ":="
          `rfl)
         (calcStep («term_=_» (Term.hole "_") "=" (Term.app `t.center_mass [`f `id])) ":=" (Term.hole "_"))])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `sub_smul)
          ","
          (Tactic.simpLemma [] [] `mul_smul)
          ","
          (Tactic.simpLemma [] [] `sum_sub_distrib)
          ","
          (Tactic.simpLemma [] ["←"] `smul_sum)
          ","
          (Tactic.simpLemma [] [] `gcombo)
          ","
          (Tactic.simpLemma [] [] `smul_zero)
          ","
          (Tactic.simpLemma [] [] `sub_zero)
          ","
          (Tactic.simpLemma [] [] `center_mass)
          ","
          (Tactic.simpLemma [] [] `fsum)
          ","
          (Tactic.simpLemma [] [] `inv_one)
          ","
          (Tactic.simpLemma [] [] `one_smul)
          ","
          (Tactic.simpLemma [] [] `id.def)]
         "]"]
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `sub_smul)
     ","
     (Tactic.simpLemma [] [] `mul_smul)
     ","
     (Tactic.simpLemma [] [] `sum_sub_distrib)
     ","
     (Tactic.simpLemma [] ["←"] `smul_sum)
     ","
     (Tactic.simpLemma [] [] `gcombo)
     ","
     (Tactic.simpLemma [] [] `smul_zero)
     ","
     (Tactic.simpLemma [] [] `sub_zero)
     ","
     (Tactic.simpLemma [] [] `center_mass)
     ","
     (Tactic.simpLemma [] [] `fsum)
     ","
     (Tactic.simpLemma [] [] `inv_one)
     ","
     (Tactic.simpLemma [] [] `one_smul)
     ","
     (Tactic.simpLemma [] [] `id.def)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id.def
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `inv_one
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `fsum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `center_mass
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `gcombo
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `smul_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sum_sub_distrib
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sub_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
       " in "
       (Term.app `t.erase [`i₀])
       ", "
       (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e))
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
       " in "
       `t
       ", "
       (Algebra.Group.Defs.«term_•_» (Term.app `k [`e]) " • " `e)))
     ":="
     (Term.app
      `sum_erase
      [(Term.hole "_")
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hk) "," (Tactic.rwRule [] `zero_smul)] "]")
             [])
            [])])))]))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
       " in "
       `t
       ", "
       (Algebra.Group.Defs.«term_•_»
        («term_-_»
         (Term.app `f [`e])
         "-"
         (Finset.Data.Finset.Fold.«term_*_»
          («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
          "*"
          (Term.app `g [`e])))
        " • "
        `e)))
     ":="
     `rfl)
    (calcStep («term_=_» (Term.hole "_") "=" (Term.app `t.center_mass [`f `id])) ":=" (Term.hole "_"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Term.hole "_") "=" (Term.app `t.center_mass [`f `id]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `t.center_mass [`f `id])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `t.center_mass
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
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.hole "_")
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
    " in "
    `t
    ", "
    (Algebra.Group.Defs.«term_•_»
     («term_-_»
      (Term.app `f [`e])
      "-"
      (Finset.Data.Finset.Fold.«term_*_»
       («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
       "*"
       (Term.app `g [`e])))
     " • "
     `e)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
   " in "
   `t
   ", "
   (Algebra.Group.Defs.«term_•_»
    («term_-_»
     (Term.app `f [`e])
     "-"
     (Finset.Data.Finset.Fold.«term_*_» («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) "*" (Term.app `g [`e])))
    " • "
    `e))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_»
   («term_-_»
    (Term.app `f [`e])
    "-"
    (Finset.Data.Finset.Fold.«term_*_» («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) "*" (Term.app `g [`e])))
   " • "
   `e)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  («term_-_»
   (Term.app `f [`e])
   "-"
   (Finset.Data.Finset.Fold.«term_*_» («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) "*" (Term.app `g [`e])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) "*" (Term.app `g [`e]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_/_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `g [`i₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `g
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 71 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 70, term))
  (Term.app `f [`i₀])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i₀
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 70 >? 1022, (some 1023, term) <=? (some 70, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 70, (some 71, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 66 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 65, term))
  (Term.app `f [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `f
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 65 >? 1022, (some 1023, term) <=? (some 65, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 65, (some 0, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(«term_-_»
   (Term.app `f [`e])
   "-"
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.paren "(" [(«term_/_» (Term.app `f [`i₀]) "/" (Term.app `g [`i₀])) []] ")")
    "*"
    (Term.app `g [`e])))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
    If `x` is in the convex hull of some finset `t` whose elements are not affine-independent,
    then it is in the convex hull of a strict subset of `t`. -/
  theorem
    mem_convex_hull_erase
    [ DecidableEq E ]
        { t : Finset E }
        ( h : ¬ AffineIndependent 𝕜 ( coeₓ : t → E ) )
        { x : E }
        ( m : x ∈ convexHull 𝕜 ( ↑ t : Set E ) )
      : ∃ y : ( ↑ t : Set E ) , x ∈ convexHull 𝕜 ( ↑ t.erase y : Set E )
    :=
      by
        simp only [ Finset.convex_hull_eq , mem_set_of_eq ] at m ⊢
          obtain ⟨ f , fpos , fsum , rfl ⟩ := m
          obtain ⟨ g , gcombo , gsum , gpos ⟩ := exists_nontrivial_relation_sum_zero_of_not_affine_ind h
          replace gpos := exists_pos_of_sum_zero_of_exists_nonzero g gsum gpos
          clear h
          let s := t.filter fun z : E => 0 < g z
          obtain ⟨ i₀ , mem , w ⟩ : ∃ i₀ ∈ s , ∀ , ∀ i ∈ s , ∀ , f i₀ / g i₀ ≤ f i / g i
          ·
            apply s.exists_min_image fun z => f z / g z
              obtain ⟨ x , hx , hgx ⟩ : ∃ x ∈ t , 0 < g x := gpos
              exact ⟨ x , mem_filter.mpr ⟨ hx , hgx ⟩ ⟩
          have hg : 0 < g i₀ := by rw [ mem_filter ] at mem exact mem . 2
          have hi₀ : i₀ ∈ t := filter_subset _ _ mem
          let k : E → 𝕜 := fun z => f z - f i₀ / g i₀ * g z
          have hk : k i₀ = 0 := by field_simp [ k , ne_of_gtₓ hg ]
          have
            ksum
              : ∑ e in t.erase i₀ , k e = 1
              :=
              by
                calc
                  ∑ e in t.erase i₀ , k e = ∑ e in t , k e
                      :=
                      by conv_rhs => rw [ ← insert_erase hi₀ , sum_insert not_mem_erase i₀ t , hk , zero_addₓ ]
                    _ = ∑ e in t , f e - f i₀ / g i₀ * g e := rfl
                    _ = 1 := by rw [ sum_sub_distrib , fsum , ← mul_sum , gsum , mul_zero , sub_zero ]
          refine' ⟨ ⟨ i₀ , hi₀ ⟩ , k , _ , ksum , _ ⟩
          ·
            simp only [ and_imp , sub_nonneg , mem_erase , Ne.def , Subtype.coe_mk ]
              intro e hei₀ het
              by_cases' hes : e ∈ s
              · have hge : 0 < g e := by rw [ mem_filter ] at hes exact hes . 2 rw [ ← le_div_iff hge ] exact w _ hes
              ·
                calc _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos _ _ _ ≤ f e := fpos e het
                  · apply div_nonneg fpos i₀ mem_of_subset filter_subset _ t mem le_of_ltₓ hg
                  · simpa only [ mem_filter , het , true_andₓ , not_ltₓ ] using hes
          ·
            simp only [ Subtype.coe_mk , center_mass_eq_of_sum_1 _ id ksum , id ]
              calc
                ∑ e in t.erase i₀ , k e • e = ∑ e in t , k e • e := sum_erase _ by rw [ hk , zero_smul ]
                  _ = ∑ e in t , f e - f i₀ / g i₀ * g e • e := rfl
                  _ = t.center_mass f id := _
              simp
                only
                [
                  sub_smul
                    ,
                    mul_smul
                    ,
                    sum_sub_distrib
                    ,
                    ← smul_sum
                    ,
                    gcombo
                    ,
                    smul_zero
                    ,
                    sub_zero
                    ,
                    center_mass
                    ,
                    fsum
                    ,
                    inv_one
                    ,
                    one_smul
                    ,
                    id.def
                  ]

variable {s : Set E} {x : E} (hx : x ∈ convexHull 𝕜 s)

include hx

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum\ncardinality, whose convex hull contains `x`. -/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `min_card_finset_of_mem_convex_hull [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Finset [`E]))])
  (Command.declValSimple
   ":="
   (Term.app
    `Function.argminOn
    [`Finset.card
     `Nat.lt_wf
     (Set.«term{_|_}»
      "{"
      `t
      "|"
      («term_∧_»
       (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
       "∧"
       (Init.Core.«term_∈_»
        `x
        " ∈ "
        (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")])))
      "}")
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpa
           "simpa"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s]))
             ","
             (Tactic.simpLemma [] [] `exists_prop)
             ","
             (Tactic.simpLemma [] [] `mem_Union)]
            "]"]
           []
           ["using" `hx])
          [])])))])
   [])
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Function.argminOn
   [`Finset.card
    `Nat.lt_wf
    (Set.«term{_|_}»
     "{"
     `t
     "|"
     («term_∧_»
      (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
      "∧"
      (Init.Core.«term_∈_»
       `x
       " ∈ "
       (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")])))
     "}")
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.simpa
          "simpa"
          []
          ["only"]
          ["["
           [(Tactic.simpLemma [] [] (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s]))
            ","
            (Tactic.simpLemma [] [] `exists_prop)
            ","
            (Tactic.simpLemma [] [] `mem_Union)]
           "]"]
          []
          ["using" `hx])
         [])])))])
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
     [(group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s]))
          ","
          (Tactic.simpLemma [] [] `exists_prop)
          ","
          (Tactic.simpLemma [] [] `mem_Union)]
         "]"]
        []
        ["using" `hx])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
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
    [(Tactic.simpLemma [] [] (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s]))
     ","
     (Tactic.simpLemma [] [] `exists_prop)
     ","
     (Tactic.simpLemma [] [] `mem_Union)]
    "]"]
   []
   ["using" `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpa', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s])
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
  `convex_hull_eq_union_convex_hull_finite_subsets
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.simpa
        "simpa"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] (Term.app `convex_hull_eq_union_convex_hull_finite_subsets [`s]))
          ","
          (Tactic.simpLemma [] [] `exists_prop)
          ","
          (Tactic.simpLemma [] [] `mem_Union)]
         "]"]
        []
        ["using" `hx])
       [])])))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}»
   "{"
   `t
   "|"
   («term_∧_»
    (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
    "∧"
    (Init.Core.«term_∈_»
     `x
     " ∈ "
     (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")])))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_∧_»
   (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
   "∧"
   (Init.Core.«term_∈_»
    `x
    " ∈ "
    (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_∧_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Core.«term_∈_»
   `x
   " ∈ "
   (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `convexHull [`𝕜 (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren "(" [`t [(Term.typeAscription ":" (Term.app `Set [`E]))]] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [`E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `𝕜
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `convexHull
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 50 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 35 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 35, term))
  (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Core.«term_⊆_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `s
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Coe.«term↑_» "↑" `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 50 >? 999, (some 999, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 36 >? 50, (some 51, term) <=? (some 35, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 35, (some 35, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.constant'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      Given a point `x` in the convex hull of a set `s`, this is a finite subset of `s` of minimum
      cardinality, whose convex hull contains `x`. -/
    noncomputable
  def
    min_card_finset_of_mem_convex_hull
    : Finset E
    :=
      Function.argminOn
        Finset.card
          Nat.lt_wf
          { t | ↑ t ⊆ s ∧ x ∈ convexHull 𝕜 ( t : Set E ) }
          by simpa only [ convex_hull_eq_union_convex_hull_finite_subsets s , exists_prop , mem_Union ] using hx

theorem min_card_finset_of_mem_convex_hull_subseteq : ↑min_card_finset_of_mem_convex_hull hx ⊆ s :=
  (Function.argmin_on_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).1

theorem mem_min_card_finset_of_mem_convex_hull : x ∈ convexHull 𝕜 (min_card_finset_of_mem_convex_hull hx : Set E) :=
  (Function.argmin_on_mem _ _ { t : Finset E | ↑t ⊆ s ∧ x ∈ convexHull 𝕜 (t : Set E) } _).2

theorem min_card_finset_of_mem_convex_hull_nonempty : (min_card_finset_of_mem_convex_hull hx).Nonempty := by
  rw [← Finset.coe_nonempty, ← @convex_hull_nonempty_iff 𝕜]
  exact ⟨x, mem_min_card_finset_of_mem_convex_hull hx⟩

theorem min_card_finset_of_mem_convex_hull_card_le_card {t : Finset E} (ht₁ : ↑t ⊆ s)
    (ht₂ : x ∈ convexHull 𝕜 (t : Set E)) : (min_card_finset_of_mem_convex_hull hx).card ≤ t.card :=
  Function.argmin_on_le _ _ _ ⟨ht₁, ht₂⟩

theorem affine_independent_min_card_finset_of_mem_convex_hull :
    AffineIndependent 𝕜 (coeₓ : min_card_finset_of_mem_convex_hull hx → E) := by
  let k := (min_card_finset_of_mem_convex_hull hx).card - 1
  have hk : (min_card_finset_of_mem_convex_hull hx).card = k+1 := by
    exact (Nat.succ_pred_eq_of_posₓ (finset.card_pos.mpr (min_card_finset_of_mem_convex_hull_nonempty hx))).symm
  classical
  by_contra
  obtain ⟨p, hp⟩ := mem_convex_hull_erase h (mem_min_card_finset_of_mem_convex_hull hx)
  have contra :=
    min_card_finset_of_mem_convex_hull_card_le_card hx
      (Set.Subset.trans (Finset.erase_subset (↑p) (min_card_finset_of_mem_convex_hull hx))
        (min_card_finset_of_mem_convex_hull_subseteq hx))
      hp
  rw [← not_ltₓ] at contra
  apply contra
  erw [card_erase_of_mem p.2, hk]
  exact lt_add_one _

end Caratheodory

variable {s : Set E}

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [(Command.docComment "/--" " **Carathéodory's convexity theorem** -/")] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `convex_hull_eq_union [])
  (Command.declSig
   []
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `convexHull [`𝕜 `s])
     "="
     (Set.Data.Set.Lattice.«term⋃_,_»
      "⋃"
      (Lean.explicitBinders
       [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `t)] ":" (Term.app `Finset [`E]) ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `hss)]
         ":"
         (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
         ")")
        (Lean.bracketedExplicitBinders
         "("
         [(Lean.binderIdent `hai)]
         ":"
         (Term.app
          `AffineIndependent
          [`𝕜 (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t "→" `E))]] ")")])
         ")")])
      ", "
      (Term.app `convexHull [`𝕜 (Init.Coe.«term↑_» "↑" `t)])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.apply "apply" `Set.Subset.antisymm) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.intro "intro" [`x `hx]) [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
              [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [(Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
                ","
                (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
                ","
                (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
                ","
                (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])]
               "⟩"))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (tacticIterate____
              "iterate"
              [(numLit "3")]
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.convert "convert" [] (Term.app `Set.Union_subset [(Term.hole "_")]) []) [])
                 (group (Tactic.intro "intro" []) [])])))
             [])
            (group (Tactic.exact "exact" (Term.app `convex_hull_mono [(«term‹_›» "‹" (Term.hole "_") "›")])) [])])))
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
     [(group (Tactic.apply "apply" `Set.Subset.antisymm) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`x `hx]) [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
             [])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
               ","
               (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
               ","
               (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
               ","
               (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])]
              "⟩"))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (tacticIterate____
             "iterate"
             [(numLit "3")]
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.convert "convert" [] (Term.app `Set.Union_subset [(Term.hole "_")]) []) [])
                (group (Tactic.intro "intro" []) [])])))
            [])
           (group (Tactic.exact "exact" (Term.app `convex_hull_mono [(«term‹_›» "‹" (Term.hole "_") "›")])) [])])))
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
       (tacticIterate____
        "iterate"
        [(numLit "3")]
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.convert "convert" [] (Term.app `Set.Union_subset [(Term.hole "_")]) []) [])
           (group (Tactic.intro "intro" []) [])])))
       [])
      (group (Tactic.exact "exact" (Term.app `convex_hull_mono [(«term‹_›» "‹" (Term.hole "_") "›")])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `convex_hull_mono [(«term‹_›» "‹" (Term.hole "_") "›")]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `convex_hull_mono [(«term‹_›» "‹" (Term.hole "_") "›")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term‹_›» "‹" (Term.hole "_") "›")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term‹_›»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.hole "_")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.hole.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `convex_hull_mono
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (tacticIterate____
   "iterate"
   [(numLit "3")]
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.convert "convert" [] (Term.app `Set.Union_subset [(Term.hole "_")]) []) [])
      (group (Tactic.intro "intro" []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticIterate____', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.intro "intro" [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert "convert" [] (Term.app `Set.Union_subset [(Term.hole "_")]) [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set.Union_subset [(Term.hole "_")])
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
  `Set.Union_subset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.intro "intro" [`x `hx]) [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.anonymousCtor
         "⟨"
         [(Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
          ","
          (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
          ","
          (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
          ","
          (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])]
         "⟩"))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.anonymousCtor
    "⟨"
    [(Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
     ","
     (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
     ","
     (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
     ","
     (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])]
    "⟩"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.anonymousCtor
   "⟨"
   [(Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
    ","
    (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
    ","
    (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
    ","
    (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])]
   "⟩")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.anonymousCtor.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Caratheodory.mem_min_card_finset_of_mem_convex_hull [`hx])
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
  `Caratheodory.mem_min_card_finset_of_mem_convex_hull
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull [`hx])
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
  `Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq [`hx])
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
  `Caratheodory.min_card_finset_of_mem_convex_hull_subseteq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Caratheodory.minCardFinsetOfMemConvexHull [`hx])
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
  `Caratheodory.minCardFinsetOfMemConvexHull
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_Union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `exists_prop
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`x `hx])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hx
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `Set.Subset.antisymm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.Subset.antisymm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `convexHull [`𝕜 `s])
   "="
   (Set.Data.Set.Lattice.«term⋃_,_»
    "⋃"
    (Lean.explicitBinders
     [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `t)] ":" (Term.app `Finset [`E]) ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `hss)]
       ":"
       (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
       ")")
      (Lean.bracketedExplicitBinders
       "("
       [(Lean.binderIdent `hai)]
       ":"
       (Term.app
        `AffineIndependent
        [`𝕜 (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t "→" `E))]] ")")])
       ")")])
    ", "
    (Term.app `convexHull [`𝕜 (Init.Coe.«term↑_» "↑" `t)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.Data.Set.Lattice.«term⋃_,_»
   "⋃"
   (Lean.explicitBinders
    [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `t)] ":" (Term.app `Finset [`E]) ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `hss)]
      ":"
      (Init.Core.«term_⊆_» (Init.Coe.«term↑_» "↑" `t) " ⊆ " `s)
      ")")
     (Lean.bracketedExplicitBinders
      "("
      [(Lean.binderIdent `hai)]
      ":"
      (Term.app `AffineIndependent [`𝕜 (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t "→" `E))]] ")")])
      ")")])
   ", "
   (Term.app `convexHull [`𝕜 (Init.Coe.«term↑_» "↑" `t)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.Data.Set.Lattice.«term⋃_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `convexHull [`𝕜 (Init.Coe.«term↑_» "↑" `t)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `t)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Coe.«term↑_» "↑" `t) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `𝕜
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `convexHull
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
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
/-- **Carathéodory's convexity theorem** -/
  theorem
    convex_hull_eq_union
    :
      convexHull 𝕜 s
        =
        ⋃ ( t : Finset E ) ( hss : ↑ t ⊆ s ) ( hai : AffineIndependent 𝕜 ( coeₓ : t → E ) ) , convexHull 𝕜 ↑ t
    :=
      by
        apply Set.Subset.antisymm
          ·
            intro x hx
              simp only [ exists_prop , Set.mem_Union ]
              exact
                ⟨
                  Caratheodory.minCardFinsetOfMemConvexHull hx
                    ,
                    Caratheodory.min_card_finset_of_mem_convex_hull_subseteq hx
                    ,
                    Caratheodory.affine_independent_min_card_finset_of_mem_convex_hull hx
                    ,
                    Caratheodory.mem_min_card_finset_of_mem_convex_hull hx
                  ⟩
          · iterate 3 convert Set.Union_subset _ intro exact convex_hull_mono ‹ _ ›

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment "/--" " A more explicit version of `convex_hull_eq_union`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `eq_pos_convex_span_of_mem_convex_hull [])
  (Command.declSig
   [(Term.implicitBinder "{" [`x] [":" `E] "}")
    (Term.explicitBinder "(" [`hx] [":" (Init.Core.«term_∈_» `x " ∈ " (Term.app `convexHull [`𝕜 `s]))] [] ")")]
   (Term.typeSpec
    ":"
    («term∃_,_»
     "∃"
     (Lean.explicitBinders
      [(Lean.bracketedExplicitBinders
        "("
        [(Lean.binderIdent `ι)]
        ":"
        (Term.sort "Sort" [(Level.addLit `u "+" (numLit "1"))])
        ")")
       (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent "_")] ":" (Term.app `Fintype [`ι]) ")")])
     ","
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.exact
           "exact"
           («term∃_,_»
            "∃"
            (Lean.explicitBinders
             [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `z)] ":" (Term.arrow `ι "→" `E) ")")
              (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `w)] ":" (Term.arrow `ι "→" `𝕜) ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent `hss)]
               ":"
               (Init.Core.«term_⊆_» (Term.app `Set.Range [`z]) " ⊆ " `s)
               ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent `hai)]
               ":"
               (Term.app `AffineIndependent [`𝕜 `z])
               ")")
              (Lean.bracketedExplicitBinders
               "("
               [(Lean.binderIdent `hw)]
               ":"
               (Term.forall "∀" [(Term.simpleBinder [`i] [])] "," («term_<_» (numLit "0") "<" (Term.app `w [`i])))
               ")")])
            ","
            («term_∧_»
             («term_=_»
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Term.app `w [`i]))
              "="
              (numLit "1"))
             "∧"
             («term_=_»
              (Algebra.BigOperators.Basic.«term∑_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] []))
               ", "
               (Algebra.Group.Defs.«term_•_» (Term.app `w [`i]) " • " (Term.app `z [`i])))
              "="
              `x))))
          [])]))))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `convex_hull_eq_union)] "]")
         [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₁)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₂)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₃)]) [])]
             "⟩")])]
         []
         [":=" [`hx]])
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["["
          [(Tactic.simpLemma [] [] `t.convex_hull_eq)
           ","
           (Tactic.simpLemma [] [] `exists_prop)
           ","
           (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
          "]"]
         [(Tactic.location "at" (Tactic.locationHyp [`ht₃] []))])
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₁)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₂)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₃)]) [])]
             "⟩")])]
         []
         [":=" [`ht₃]])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `t'
           []
           ":="
           (Term.app
            `t.filter
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" («term_≠_» (Term.app `w [`i]) "≠" (numLit "0"))))]))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.anonymousCtor
          "⟨"
          [`t'
           ","
           `t'.fintype_coe_sort
           ","
           (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t' "→" `E))]] ")")
           ","
           («term_∘_» `w "∘" (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t' "→" `E))]] ")"))
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")
           ","
           (Term.hole "_")
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
           [(group
             (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.range_coe_subtype)] "]") [])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.app `subset.trans [(Term.app `Finset.filter_subset [(Term.hole "_") `t]) `ht₁]))
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
              (Term.app
               `ht₂.comp_embedding
               [(Term.anonymousCtor
                 "⟨"
                 [(Term.hole "_")
                  ","
                  (Term.app
                   `inclusion_injective
                   [(Term.app
                     `Finset.filter_subset
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`i] [])]
                        "=>"
                        («term_≠_» (Term.app `w [`i]) "≠" (numLit "0"))))
                      `t])])]
                 "⟩")]))
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
                [(Term.simpleBinder [`i] [])]
                "=>"
                (Term.app
                 (Term.proj
                  (Term.app
                   `hw₁
                   [(Term.hole "_")
                    (Term.proj
                     (Term.app `finset.mem_filter.mp [(Term.proj `i "." (fieldIdx "2"))])
                     "."
                     (fieldIdx "1"))])
                  "."
                  `lt_of_ne)
                 [(Term.proj
                   (Term.proj (Term.app `finset.mem_filter.mp [`i.property]) "." (fieldIdx "2"))
                   "."
                   `symm)]))))
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Finset.sum_attach)
                ","
                (Tactic.rwRule [] `Finset.sum_filter_ne_zero)
                ","
                (Tactic.rwRule [] `hw₂)]
               "]")
              [])
             [])])))
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.change
              "change"
              («term_=_»
               (Algebra.BigOperators.Basic.«term∑_in_,_»
                "∑"
                (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
                " in "
                `t'.attach
                ", "
                (Term.app
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`e] [])]
                   "=>"
                   (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
                 [(Init.Coe.«term↑_» "↑" `i)]))
               "="
               `x)
              [])
             [])
            (group
             (Tactic.tacticErw__
              "erw"
              (Tactic.rwRuleSeq
               "["
               [(Tactic.rwRule [] `Finset.sum_attach) "," (Tactic.rwRule [] `Finset.sum_filter_of_ne)]
               "]")
              [])
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂]))] "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hw₃] []))])
                  [])
                 (group (Tactic.exact "exact" `hw₃) [])])))
             [])
            (group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.intro "intro" [`e `he `hwe `contra]) [])
                 (group (Tactic.apply "apply" `hwe) [])
                 (group
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `contra) "," (Tactic.rwRule [] `zero_smul)] "]")
                   [])
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
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `convex_hull_eq_union)] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `exists_prop) "," (Tactic.simpLemma [] [] `Set.mem_Union)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `t)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₁)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₂)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ht₃)]) [])]
            "⟩")])]
        []
        [":=" [`hx]])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `t.convex_hull_eq)
          ","
          (Tactic.simpLemma [] [] `exists_prop)
          ","
          (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
         "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`ht₃] []))])
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `w)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₁)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₂)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `hw₃)]) [])]
            "⟩")])]
        []
        [":=" [`ht₃]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `t'
          []
          ":="
          (Term.app
           `t.filter
           [(Term.fun
             "fun"
             (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" («term_≠_» (Term.app `w [`i]) "≠" (numLit "0"))))]))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.anonymousCtor
         "⟨"
         [`t'
          ","
          `t'.fintype_coe_sort
          ","
          (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t' "→" `E))]] ")")
          ","
          («term_∘_» `w "∘" (Term.paren "(" [`coeₓ [(Term.typeAscription ":" (Term.arrow `t' "→" `E))]] ")"))
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")
          ","
          (Term.hole "_")
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
          [(group
            (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Subtype.range_coe_subtype)] "]") [])
            [])
           (group
            (Tactic.exact "exact" (Term.app `subset.trans [(Term.app `Finset.filter_subset [(Term.hole "_") `t]) `ht₁]))
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
             (Term.app
              `ht₂.comp_embedding
              [(Term.anonymousCtor
                "⟨"
                [(Term.hole "_")
                 ","
                 (Term.app
                  `inclusion_injective
                  [(Term.app
                    `Finset.filter_subset
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`i] [])]
                       "=>"
                       («term_≠_» (Term.app `w [`i]) "≠" (numLit "0"))))
                     `t])])]
                "⟩")]))
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
               [(Term.simpleBinder [`i] [])]
               "=>"
               (Term.app
                (Term.proj
                 (Term.app
                  `hw₁
                  [(Term.hole "_")
                   (Term.proj (Term.app `finset.mem_filter.mp [(Term.proj `i "." (fieldIdx "2"))]) "." (fieldIdx "1"))])
                 "."
                 `lt_of_ne)
                [(Term.proj
                  (Term.proj (Term.app `finset.mem_filter.mp [`i.property]) "." (fieldIdx "2"))
                  "."
                  `symm)]))))
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Finset.sum_attach)
               ","
               (Tactic.rwRule [] `Finset.sum_filter_ne_zero)
               ","
               (Tactic.rwRule [] `hw₂)]
              "]")
             [])
            [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.change
             "change"
             («term_=_»
              (Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
               " in "
               `t'.attach
               ", "
               (Term.app
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`e] [])]
                  "=>"
                  (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
                [(Init.Coe.«term↑_» "↑" `i)]))
              "="
              `x)
             [])
            [])
           (group
            (Tactic.tacticErw__
             "erw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Finset.sum_attach) "," (Tactic.rwRule [] `Finset.sum_filter_of_ne)]
              "]")
             [])
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂]))] "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hw₃] []))])
                 [])
                (group (Tactic.exact "exact" `hw₃) [])])))
            [])
           (group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.intro "intro" [`e `he `hwe `contra]) [])
                (group (Tactic.apply "apply" `hwe) [])
                (group
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `contra) "," (Tactic.rwRule [] `zero_smul)] "]")
                  [])
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
     [(group
       (Tactic.change
        "change"
        («term_=_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
          " in "
          `t'.attach
          ", "
          (Term.app
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`e] [])]
             "=>"
             (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
           [(Init.Coe.«term↑_» "↑" `i)]))
         "="
         `x)
        [])
       [])
      (group
       (Tactic.tacticErw__
        "erw"
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] `Finset.sum_attach) "," (Tactic.rwRule [] `Finset.sum_filter_of_ne)]
         "]")
        [])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂]))] "]")
             [(Tactic.location "at" (Tactic.locationHyp [`hw₃] []))])
            [])
           (group (Tactic.exact "exact" `hw₃) [])])))
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.intro "intro" [`e `he `hwe `contra]) [])
           (group (Tactic.apply "apply" `hwe) [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `contra) "," (Tactic.rwRule [] `zero_smul)] "]")
             [])
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
     [(group (Tactic.intro "intro" [`e `he `hwe `contra]) [])
      (group (Tactic.apply "apply" `hwe) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `contra) "," (Tactic.rwRule [] `zero_smul)] "]")
        [])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `contra) "," (Tactic.rwRule [] `zero_smul)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `zero_smul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `contra
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `hwe)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hwe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`e `he `hwe `contra])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.intro', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `contra
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hwe
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `he
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `e
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
     [(group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂]))] "]")
        [(Tactic.location "at" (Tactic.locationHyp [`hw₃] []))])
       [])
      (group (Tactic.exact "exact" `hw₃) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `hw₃)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hw₃
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂]))] "]")
   [(Tactic.location "at" (Tactic.locationHyp [`hw₃] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hw₃
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `t.center_mass_eq_of_sum_1 [`id `hw₂])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hw₂
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `id
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `t.center_mass_eq_of_sum_1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticErw__
   "erw"
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Finset.sum_attach) "," (Tactic.rwRule [] `Finset.sum_filter_of_ne)] "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticErw__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_filter_of_ne
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.change
   "change"
   («term_=_»
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
     " in "
     `t'.attach
     ", "
     (Term.app
      (Term.fun
       "fun"
       (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
      [(Init.Coe.«term↑_» "↑" `i)]))
    "="
    `x)
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.change', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
    " in "
    `t'.attach
    ", "
    (Term.app
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
     [(Init.Coe.«term↑_» "↑" `i)]))
   "="
   `x)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `x
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `i)] [":" `t']))
   " in "
   `t'.attach
   ", "
   (Term.app
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
    [(Init.Coe.«term↑_» "↑" `i)]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.fun
    "fun"
    (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
   [(Init.Coe.«term↑_» "↑" `i)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `i)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Coe.«term↑_» "↑" `i) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.Group.Defs.«term_•_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 73 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 73, term))
  (Term.app `w [`e])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `w
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 74 >? 1022, (some 1023, term) <=? (some 73, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 73, (some 73, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Algebra.Group.Defs.«term_•_» (Term.app `w [`e]) " • " `e)))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `t'.attach
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
/-- A more explicit version of `convex_hull_eq_union`. -/
  theorem
    eq_pos_convex_span_of_mem_convex_hull
    { x : E } ( hx : x ∈ convexHull 𝕜 s )
      :
        ∃
          ( ι : Sort u + 1 ) ( _ : Fintype ι )
          ,
          by
            exact
              ∃
                ( z : ι → E )
                  ( w : ι → 𝕜 )
                  ( hss : Set.Range z ⊆ s )
                  ( hai : AffineIndependent 𝕜 z )
                  ( hw : ∀ i , 0 < w i )
                ,
                ∑ i , w i = 1 ∧ ∑ i , w i • z i = x
    :=
      by
        rw [ convex_hull_eq_union ] at hx
          simp only [ exists_prop , Set.mem_Union ] at hx
          obtain ⟨ t , ht₁ , ht₂ , ht₃ ⟩ := hx
          simp only [ t.convex_hull_eq , exists_prop , Set.mem_set_of_eq ] at ht₃
          obtain ⟨ w , hw₁ , hw₂ , hw₃ ⟩ := ht₃
          let t' := t.filter fun i => w i ≠ 0
          refine' ⟨ t' , t'.fintype_coe_sort , ( coeₓ : t' → E ) , w ∘ ( coeₓ : t' → E ) , _ , _ , _ , _ , _ ⟩
          · rw [ Subtype.range_coe_subtype ] exact subset.trans Finset.filter_subset _ t ht₁
          · exact ht₂.comp_embedding ⟨ _ , inclusion_injective Finset.filter_subset fun i => w i ≠ 0 t ⟩
          · exact fun i => hw₁ _ finset.mem_filter.mp i . 2 . 1 . lt_of_ne finset.mem_filter.mp i.property . 2 . symm
          · erw [ Finset.sum_attach , Finset.sum_filter_ne_zero , hw₂ ]
          ·
            change ∑ i : t' in t'.attach , fun e => w e • e ↑ i = x
              erw [ Finset.sum_attach , Finset.sum_filter_of_ne ]
              · rw [ t.center_mass_eq_of_sum_1 id hw₂ ] at hw₃ exact hw₃
              · intro e he hwe contra apply hwe rw [ contra , zero_smul ]

