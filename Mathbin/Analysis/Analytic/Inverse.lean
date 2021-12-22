import Mathbin.Analysis.Analytic.Composition

/-!

# Inverse of analytic functions

We construct the left and right inverse of a formal multilinear series with invertible linear term,
we prove that they coincide and study their properties (notably convergence).

## Main statements

* `p.left_inv i`: the formal left inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.right_inv i`: the formal right inverse of the formal multilinear series `p`,
  for `i : E ≃L[𝕜] F` which coincides with `p₁`.
* `p.left_inv_comp` says that `p.left_inv i` is indeed a left inverse to `p` when `p₁ = i`.
* `p.right_inv_comp` says that `p.right_inv i` is indeed a right inverse to `p` when `p₁ = i`.
* `p.left_inv_eq_right_inv`: the two inverses coincide.
* `p.radius_right_inv_pos_of_radius_pos`: if a power series has a positive radius of convergence,
  then so does its inverse.

-/


open_locale BigOperators Classical TopologicalSpace

open Finset Filter

namespace FormalMultilinearSeries

variable {𝕜 : Type _} [NondiscreteNormedField 𝕜] {E : Type _} [NormedGroup E] [NormedSpace 𝕜 E] {F : Type _}
  [NormedGroup F] [NormedSpace 𝕜 F]

/-! ### The left inverse of a formal multilinear series -/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The left inverse of a formal multilinear series, where the `n`-th term is defined inductively\nin terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term\n`p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should\ncoincide with `p₁`, so that one can use its inverse in the construction. The definition does not\nuse that `i = p₁`, but proofs that the definition is well-behaved do.\n\nThe `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this\nexpression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this\nterm compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.\n\nThese formulas only make sense when the constant term `p₀` vanishes. The definition we give is\ngeneral, but it ignores the value of `p₀`.\n-/")]
  []
  []
  [(Command.noncomputable "noncomputable")]
  []
  [])
 (Command.def
  "def"
  (Command.declId `left_inv [])
  (Command.optDeclSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")]
   [(Term.typeSpec ":" (Term.app `FormalMultilinearSeries [`𝕜 `F `E]))])
  (Command.declValEqns
   (Term.matchAltsWhereDecls
    (Term.matchAlts
     [(Term.matchAlt "|" [(numLit "0")] "=>" (numLit "0"))
      (Term.matchAlt
       "|"
       [(numLit "1")]
       "=>"
       (Term.app (Term.proj (Term.app `continuousMultilinearCurryFin1 [`𝕜 `F `E]) "." `symm) [`i.symm]))
      (Term.matchAlt
       "|"
       [(Init.Logic.«term_+_» `n "+" (numLit "2"))]
       "=>"
       («term-_»
        "-"
        (Algebra.BigOperators.Basic.«term∑_,_»
         "∑"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `c)]
           [":"
            («term{__:_//_}»
             "{"
             `c
             [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]
             "//"
             («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
             "}")]))
         ", "
         (Term.have
          "have"
          (Term.haveDecl
           (Term.haveIdDecl
            []
            [(Term.typeSpec
              ":"
              («term_<_»
               (Term.proj
                (Term.paren
                 "("
                 [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
                 ")")
                "."
                `length)
               "<"
               (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
            ":="
            (Term.proj `c "." (fieldIdx "2"))))
          []
          (Term.app
           (Term.proj
            (Term.app
             `left_inv
             [(Term.proj
               (Term.paren
                "("
                [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
                ")")
               "."
               `length)])
            "."
            `compAlongComposition)
           [(Term.app `p.comp_continuous_linear_map [`i.symm]) `c])))))])
    []))
  []
  []
  []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declaration', expected 'Lean.Parser.Command.declaration.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.def.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValSimple'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.declValEqns.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAltsWhereDecls', expected 'Lean.Parser.Term.matchAltsWhereDecls.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlts', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.matchAlt', expected 'Lean.Parser.Term.matchAlt.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_»
   "-"
   (Algebra.BigOperators.Basic.«term∑_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `c)]
      [":"
       («term{__:_//_}»
        "{"
        `c
        [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]
        "//"
        («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
        "}")]))
    ", "
    (Term.have
     "have"
     (Term.haveDecl
      (Term.haveIdDecl
       []
       [(Term.typeSpec
         ":"
         («term_<_»
          (Term.proj
           (Term.paren
            "("
            [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
            ")")
           "."
           `length)
          "<"
          (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
       ":="
       (Term.proj `c "." (fieldIdx "2"))))
     []
     (Term.app
      (Term.proj
       (Term.app
        `left_inv
        [(Term.proj
          (Term.paren
           "("
           [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
           ")")
          "."
          `length)])
       "."
       `compAlongComposition)
      [(Term.app `p.comp_continuous_linear_map [`i.symm]) `c]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `c)]
     [":"
      («term{__:_//_}»
       "{"
       `c
       [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]
       "//"
       («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
       "}")]))
   ", "
   (Term.have
    "have"
    (Term.haveDecl
     (Term.haveIdDecl
      []
      [(Term.typeSpec
        ":"
        («term_<_»
         (Term.proj
          (Term.paren
           "("
           [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
           ")")
          "."
          `length)
         "<"
         (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
      ":="
      (Term.proj `c "." (fieldIdx "2"))))
    []
    (Term.app
     (Term.proj
      (Term.app
       `left_inv
       [(Term.proj
         (Term.paren
          "("
          [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
          ")")
         "."
         `length)])
      "."
      `compAlongComposition)
     [(Term.app `p.comp_continuous_linear_map [`i.symm]) `c])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.have
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     []
     [(Term.typeSpec
       ":"
       («term_<_»
        (Term.proj
         (Term.paren
          "("
          [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
          ")")
         "."
         `length)
        "<"
        (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
     ":="
     (Term.proj `c "." (fieldIdx "2"))))
   []
   (Term.app
    (Term.proj
     (Term.app
      `left_inv
      [(Term.proj
        (Term.paren
         "("
         [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
         ")")
        "."
        `length)])
     "."
     `compAlongComposition)
    [(Term.app `p.comp_continuous_linear_map [`i.symm]) `c]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.have', expected 'Lean.Parser.Term.have.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.app
     `left_inv
     [(Term.proj
       (Term.paren
        "("
        [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
        ")")
       "."
       `length)])
    "."
    `compAlongComposition)
   [(Term.app `p.comp_continuous_linear_map [`i.symm]) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.comp_continuous_linear_map [`i.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.comp_continuous_linear_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.comp_continuous_linear_map [`i.symm]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj
   (Term.app
    `left_inv
    [(Term.proj
      (Term.paren
       "("
       [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
       ")")
      "."
      `length)])
   "."
   `compAlongComposition)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `left_inv
   [(Term.proj
     (Term.paren
      "("
      [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
      ")")
     "."
     `length)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Term.paren
    "("
    [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
    ")")
   "."
   `length)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `left_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `left_inv
   [(Term.proj
     (Term.paren
      "("
      [`c
       [(Term.typeAscription
         ":"
         (Term.app `Composition [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")]))]]
      ")")
     "."
     `length)])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, term))
  (Term.proj `c "." (fieldIdx "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_»
   (Term.proj
    (Term.paren
     "("
     [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
     ")")
    "."
    `length)
   "<"
   (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.proj
   (Term.paren
    "("
    [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
    ")")
   "."
   `length)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [`c [(Term.typeAscription ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1023, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValEqns', expected 'Lean.Parser.Command.whereStructInst'
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
      The left inverse of a formal multilinear series, where the `n`-th term is defined inductively
      in terms of the previous ones to make sure that `(left_inv p i) ∘ p = id`. For this, the linear term
      `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
      coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
      use that `i = p₁`, but proofs that the definition is well-behaved do.
      
      The `n`-th term in `q ∘ p` is `∑ qₖ (p_{j₁}, ..., p_{jₖ})` over `j₁ + ... + jₖ = n`. In this
      expression, `qₙ` appears only once, in `qₙ (p₁, ..., p₁)`. We adjust the definition so that this
      term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.
      
      These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
      general, but it ignores the value of `p₀`.
      -/
    noncomputable
  def
    left_inv
    ( p : FormalMultilinearSeries 𝕜 E F ) ( i : E ≃L[ 𝕜 ] F ) : FormalMultilinearSeries 𝕜 F E
    | 0 => 0
      | 1 => continuousMultilinearCurryFin1 𝕜 F E . symm i.symm
      |
        n + 2
        =>
        -
          ∑
            c : { c : Composition n + 2 // c.length < n + 2 }
            ,
            have
              : ( c : Composition n + 2 ) . length < n + 2 := c . 2
              left_inv ( c : Composition n + 2 ) . length . compAlongComposition p.comp_continuous_linear_map i.symm c

@[simp]
theorem left_inv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : p.left_inv i 0 = 0 := by
  rw [left_inv]

@[simp]
theorem left_inv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.left_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by
  rw [left_inv]

/--  The left inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem left_inv_remove_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.remove_zero.left_inv i = p.left_inv i := by
  ext1 n
  induction' n using Nat.strongRec' with n IH
  cases n
  ·
    simp
  cases n
  ·
    simp
  simp only [left_inv, neg_inj]
  refine' Finset.sum_congr rfl fun c cuniv => _
  rcases c with ⟨c, hc⟩
  ext v
  dsimp
  simp [IH _ hc]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " The left inverse to a formal multilinear series is indeed a left inverse, provided its linear\nterm is invertible. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `left_inv_comp [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")
    (Term.explicitBinder
     "("
     [`h]
     [":"
      («term_=_»
       (Term.app `p [(numLit "1")])
       "="
       (Term.app (Term.proj (Term.app `continuousMultilinearCurryFin1 [`𝕜 `E `F]) "." `symm) [`i]))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_» (Term.app (Term.proj (Term.app `left_inv [`p `i]) "." `comp) [`p]) "=" (Term.app `id [`𝕜 `E]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `n) (Tactic.rcasesPat.one `v)] []) [])
       (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
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
               [(Tactic.simpLemma [] [] `left_inv)
                ","
                (Tactic.simpLemma [] [] `ContinuousMultilinearMap.zero_apply)
                ","
                (Tactic.simpLemma [] [] `id_apply_ne_one)
                ","
                (Tactic.simpLemma [] [] `Ne.def)
                ","
                (Tactic.simpLemma [] [] `not_false_iff)
                ","
                (Tactic.simpLemma [] [] `zero_ne_one)
                ","
                (Tactic.simpLemma [] [] `comp_coeff_zero')]
               "]"]
              [])
             [])])))
        [])
       (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
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
               [(Tactic.simpLemma [] [] `left_inv)
                ","
                (Tactic.simpLemma [] [] `comp_coeff_one)
                ","
                (Tactic.simpLemma [] [] `h)
                ","
                (Tactic.simpLemma [] [] `id_apply_one)
                ","
                (Tactic.simpLemma [] [] `ContinuousLinearEquiv.coe_apply)
                ","
                (Tactic.simpLemma [] [] `ContinuousLinearEquiv.symm_apply_apply)
                ","
                (Tactic.simpLemma [] [] `continuous_multilinear_curry_fin1_symm_apply)]
               "]"]
              [])
             [])])))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`A []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.paren
               "("
               [`Finset.univ
                [(Term.typeAscription
                  ":"
                  (Term.app `Finset [(Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))]]
               ")")
              "="
              (Init.Core.«term_∪_»
               (Term.proj
                (Set.«term{_|_}»
                 "{"
                 `c
                 "|"
                 («term_<_» (Term.app `Composition.length [`c]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                 "}")
                "."
                `toFinset)
               " ∪ "
               (Set.«term{_}» "{" [(Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))])] "}"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `subset.antisymm
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))
                   (Term.app `subset_univ [(Term.hole "_")])]))
                [])
               (group
                (Tactic.byCases'
                 "by_cases'"
                 [`h ":"]
                 («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
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
                      []
                      ["["
                       [(Tactic.simpLemma
                         []
                         []
                         (Term.app
                          (Term.proj `Composition.eq_ones_iff_le_length "." (fieldIdx "2"))
                          [(Term.app (Term.proj `not_ltₓ "." (fieldIdx "1")) [`h])]))]
                       "]"]
                      [])
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`B []]
           [(Term.typeSpec
             ":"
             (Term.app
              `Disjoint
              [(Term.proj
                (Term.paren
                 "("
                 [(Set.«term{_|_}»
                   "{"
                   `c
                   "|"
                   («term_<_» (Term.app `Composition.length [`c]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                   "}")
                  [(Term.typeAscription
                    ":"
                    (Term.app `Set [(Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))]]
                 ")")
                "."
                `toFinset)
               (Set.«term{_}» "{" [(Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))])] "}")]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`C []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (Term.app
                `p.left_inv
                [`i (Term.proj (Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))]) "." `length)])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder
                    [`j]
                    [(Term.typeSpec
                      ":"
                      (Term.app `Finₓ [(Term.proj (Term.app `Composition.ones [`n.succ.succ]) "." `length)]))])]
                  "=>"
                  (Term.app
                   `p
                   [(numLit "1")
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`k] [])]
                      "=>"
                      (Term.app
                       `v
                       [(Term.app
                         (Term.app `Finₓ.castLe [(Term.app `Composition.length_le [(Term.hole "_")])])
                         [`j])])))])))])
              "="
              (Term.app
               `p.left_inv
               [`i
                (Init.Logic.«term_+_» `n "+" (numLit "2"))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder
                    [`j]
                    [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                  "=>"
                  (Term.app
                   `p
                   [(numLit "1")
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.apply
                 "apply"
                 (Term.app
                  `FormalMultilinearSeries.congr
                  [(Term.hole "_")
                   (Term.app `Composition.ones_length [(Term.hole "_")])
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  `FormalMultilinearSeries.congr
                  [(Term.hole "_")
                   `rfl
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`k `hk1 `hk2] [])]
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.congr "congr" [] []) [])])))))]))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`D []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               `p.left_inv
               [`i
                (Init.Logic.«term_+_» `n "+" (numLit "2"))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder
                    [`j]
                    [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                  "=>"
                  (Term.app
                   `p
                   [(numLit "1")
                    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])
              "="
              («term-_»
               "-"
               (Algebra.BigOperators.Basic.«term∑_in_,_»
                "∑"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders
                  [(Lean.binderIdent `c)]
                  [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
                " in "
                (Term.proj
                 (Set.«term{_|_}»
                  "{"
                  (Mathlib.ExtendedBinder.extBinder
                   `c
                   [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
                  "|"
                  («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                  "}")
                 "."
                 `toFinset)
                ", "
                (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])])))))]
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
                 ["["
                  [(Tactic.simpLemma [] [] `left_inv)
                   ","
                   (Tactic.simpLemma [] [] `ContinuousMultilinearMap.neg_apply)
                   ","
                   (Tactic.simpLemma [] [] `neg_inj)
                   ","
                   (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                  "]"]
                 [])
                [])
               (group
                (Tactic.convert
                 "convert"
                 []
                 (Term.app
                  (Term.proj
                   (Term.proj
                    (Term.app
                     `sum_to_finset_eq_subtype
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder
                          [`c]
                          [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                        "=>"
                        («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
                      (Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder
                          [`c]
                          [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                        "=>"
                        (Term.app
                         (Term.app
                          `ContinuousMultilinearMap.compAlongComposition
                          [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
                           `c
                           (Term.app `p.left_inv [`i `c.length])])
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder
                              [`j]
                              [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                            "=>"
                            (Term.app
                             `p
                             [(numLit "1")
                              (Term.fun
                               "fun"
                               (Term.basicFun
                                [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                                "=>"
                                (Term.app `v [`j])))])))])))])
                    "."
                    `symm)
                   "."
                   `trans)
                  [(Term.hole "_")])
                 [])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 ["only"]
                 ["["
                  [(Tactic.simpLemma [] [] `comp_continuous_linear_map_apply_composition)
                   ","
                   (Tactic.simpLemma [] [] `ContinuousMultilinearMap.comp_along_composition_apply)]
                  "]"]
                 [])
                [])
               (group (Tactic.congr "congr" [] []) [])
               (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `c)] []) [])
               (group (Tactic.congr "congr" [] []) [])
               (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `k)] []) [])
               (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])]))))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
           ","
           (Tactic.simpLemma
            []
            []
            (Term.show
             "show"
             («term_≠_» (Init.Logic.«term_+_» `n "+" (numLit "2")) "≠" (numLit "1"))
             (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))
           ","
           (Tactic.simpLemma [] [] `A)
           ","
           (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
           ","
           (Tactic.simpLemma [] [] `apply_composition_ones)
           ","
           (Tactic.simpLemma [] [] `C)
           ","
           (Tactic.simpLemma [] [] `D)]
          "]"]
         [])
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
     [(group (Tactic.ext "ext" [(Tactic.rcasesPat.one `n) (Tactic.rcasesPat.one `v)] []) [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
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
              [(Tactic.simpLemma [] [] `left_inv)
               ","
               (Tactic.simpLemma [] [] `ContinuousMultilinearMap.zero_apply)
               ","
               (Tactic.simpLemma [] [] `id_apply_ne_one)
               ","
               (Tactic.simpLemma [] [] `Ne.def)
               ","
               (Tactic.simpLemma [] [] `not_false_iff)
               ","
               (Tactic.simpLemma [] [] `zero_ne_one)
               ","
               (Tactic.simpLemma [] [] `comp_coeff_zero')]
              "]"]
             [])
            [])])))
       [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
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
              [(Tactic.simpLemma [] [] `left_inv)
               ","
               (Tactic.simpLemma [] [] `comp_coeff_one)
               ","
               (Tactic.simpLemma [] [] `h)
               ","
               (Tactic.simpLemma [] [] `id_apply_one)
               ","
               (Tactic.simpLemma [] [] `ContinuousLinearEquiv.coe_apply)
               ","
               (Tactic.simpLemma [] [] `ContinuousLinearEquiv.symm_apply_apply)
               ","
               (Tactic.simpLemma [] [] `continuous_multilinear_curry_fin1_symm_apply)]
              "]"]
             [])
            [])])))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`A []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren
              "("
              [`Finset.univ
               [(Term.typeAscription
                 ":"
                 (Term.app `Finset [(Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))]]
              ")")
             "="
             (Init.Core.«term_∪_»
              (Term.proj
               (Set.«term{_|_}»
                "{"
                `c
                "|"
                («term_<_» (Term.app `Composition.length [`c]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                "}")
               "."
               `toFinset)
              " ∪ "
              (Set.«term{_}» "{" [(Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))])] "}"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `subset.antisymm
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))
                  (Term.app `subset_univ [(Term.hole "_")])]))
               [])
              (group
               (Tactic.byCases'
                "by_cases'"
                [`h ":"]
                («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
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
                     []
                     ["["
                      [(Tactic.simpLemma
                        []
                        []
                        (Term.app
                         (Term.proj `Composition.eq_ones_iff_le_length "." (fieldIdx "2"))
                         [(Term.app (Term.proj `not_ltₓ "." (fieldIdx "1")) [`h])]))]
                      "]"]
                     [])
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`B []]
          [(Term.typeSpec
            ":"
            (Term.app
             `Disjoint
             [(Term.proj
               (Term.paren
                "("
                [(Set.«term{_|_}»
                  "{"
                  `c
                  "|"
                  («term_<_» (Term.app `Composition.length [`c]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                  "}")
                 [(Term.typeAscription
                   ":"
                   (Term.app `Set [(Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))]]
                ")")
               "."
               `toFinset)
              (Set.«term{_}» "{" [(Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))])] "}")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`C []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app
              (Term.app
               `p.left_inv
               [`i (Term.proj (Term.app `Composition.ones [(Init.Logic.«term_+_» `n "+" (numLit "2"))]) "." `length)])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder
                   [`j]
                   [(Term.typeSpec
                     ":"
                     (Term.app `Finₓ [(Term.proj (Term.app `Composition.ones [`n.succ.succ]) "." `length)]))])]
                 "=>"
                 (Term.app
                  `p
                  [(numLit "1")
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`k] [])]
                     "=>"
                     (Term.app
                      `v
                      [(Term.app
                        (Term.app `Finₓ.castLe [(Term.app `Composition.length_le [(Term.hole "_")])])
                        [`j])])))])))])
             "="
             (Term.app
              `p.left_inv
              [`i
               (Init.Logic.«term_+_» `n "+" (numLit "2"))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder
                   [`j]
                   [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                 "=>"
                 (Term.app
                  `p
                  [(numLit "1")
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.apply
                "apply"
                (Term.app
                 `FormalMultilinearSeries.congr
                 [(Term.hole "_")
                  (Term.app `Composition.ones_length [(Term.hole "_")])
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `FormalMultilinearSeries.congr
                 [(Term.hole "_")
                  `rfl
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`k `hk1 `hk2] [])]
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.congr "congr" [] []) [])])))))]))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`D []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app
              `p.left_inv
              [`i
               (Init.Logic.«term_+_» `n "+" (numLit "2"))
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder
                   [`j]
                   [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                 "=>"
                 (Term.app
                  `p
                  [(numLit "1")
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])
             "="
             («term-_»
              "-"
              (Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `c)]
                 [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
               " in "
               (Term.proj
                (Set.«term{_|_}»
                 "{"
                 (Mathlib.ExtendedBinder.extBinder
                  `c
                  [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
                 "|"
                 («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
                 "}")
                "."
                `toFinset)
               ", "
               (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])])))))]
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
                ["["
                 [(Tactic.simpLemma [] [] `left_inv)
                  ","
                  (Tactic.simpLemma [] [] `ContinuousMultilinearMap.neg_apply)
                  ","
                  (Tactic.simpLemma [] [] `neg_inj)
                  ","
                  (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
                 "]"]
                [])
               [])
              (group
               (Tactic.convert
                "convert"
                []
                (Term.app
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `sum_to_finset_eq_subtype
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder
                         [`c]
                         [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                       "=>"
                       («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder
                         [`c]
                         [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                       "=>"
                       (Term.app
                        (Term.app
                         `ContinuousMultilinearMap.compAlongComposition
                         [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
                          `c
                          (Term.app `p.left_inv [`i `c.length])])
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder
                             [`j]
                             [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                           "=>"
                           (Term.app
                            `p
                            [(numLit "1")
                             (Term.fun
                              "fun"
                              (Term.basicFun
                               [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                               "=>"
                               (Term.app `v [`j])))])))])))])
                   "."
                   `symm)
                  "."
                  `trans)
                 [(Term.hole "_")])
                [])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `comp_continuous_linear_map_apply_composition)
                  ","
                  (Tactic.simpLemma [] [] `ContinuousMultilinearMap.comp_along_composition_apply)]
                 "]"]
                [])
               [])
              (group (Tactic.congr "congr" [] []) [])
              (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `c)] []) [])
              (group (Tactic.congr "congr" [] []) [])
              (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `k)] []) [])
              (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])]))))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
          ","
          (Tactic.simpLemma
           []
           []
           (Term.show
            "show"
            («term_≠_» (Init.Logic.«term_+_» `n "+" (numLit "2")) "≠" (numLit "1"))
            (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))
          ","
          (Tactic.simpLemma [] [] `A)
          ","
          (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
          ","
          (Tactic.simpLemma [] [] `apply_composition_ones)
          ","
          (Tactic.simpLemma [] [] `C)
          ","
          (Tactic.simpLemma [] [] `D)]
         "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
     ","
     (Tactic.simpLemma
      []
      []
      (Term.show
       "show"
       («term_≠_» (Init.Logic.«term_+_» `n "+" (numLit "2")) "≠" (numLit "1"))
       (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))))
     ","
     (Tactic.simpLemma [] [] `A)
     ","
     (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
     ","
     (Tactic.simpLemma [] [] `apply_composition_ones)
     ","
     (Tactic.simpLemma [] [] `C)
     ","
     (Tactic.simpLemma [] [] `D)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `D
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `apply_composition_ones
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_union [`B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_≠_» (Init.Logic.«term_+_» `n "+" (numLit "2")) "≠" (numLit "1"))
   (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.show', expected 'Lean.Parser.Term.show.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.fromTerm'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.decide "decide")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'Lean.Parser.Tactic.decide.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_≠_» (Init.Logic.«term_+_» `n "+" (numLit "2")) "≠" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≠_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `FormalMultilinearSeries.comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`D []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app
         `p.left_inv
         [`i
          (Init.Logic.«term_+_» `n "+" (numLit "2"))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder
              [`j]
              [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
            "=>"
            (Term.app
             `p
             [(numLit "1") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])
        "="
        («term-_»
         "-"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders
           (Lean.unbracketedExplicitBinders
            [(Lean.binderIdent `c)]
            [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
          " in "
          (Term.proj
           (Set.«term{_|_}»
            "{"
            (Mathlib.ExtendedBinder.extBinder
             `c
             [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
            "|"
            («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
            "}")
           "."
           `toFinset)
          ", "
          (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])])))))]
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
           ["["
            [(Tactic.simpLemma [] [] `left_inv)
             ","
             (Tactic.simpLemma [] [] `ContinuousMultilinearMap.neg_apply)
             ","
             (Tactic.simpLemma [] [] `neg_inj)
             ","
             (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
            "]"]
           [])
          [])
         (group
          (Tactic.convert
           "convert"
           []
           (Term.app
            (Term.proj
             (Term.proj
              (Term.app
               `sum_to_finset_eq_subtype
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder
                    [`c]
                    [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                  "=>"
                  («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder
                    [`c]
                    [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                  "=>"
                  (Term.app
                   (Term.app
                    `ContinuousMultilinearMap.compAlongComposition
                    [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
                     `c
                     (Term.app `p.left_inv [`i `c.length])])
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder
                        [`j]
                        [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                      "=>"
                      (Term.app
                       `p
                       [(numLit "1")
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                          "=>"
                          (Term.app `v [`j])))])))])))])
              "."
              `symm)
             "."
             `trans)
            [(Term.hole "_")])
           [])
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `comp_continuous_linear_map_apply_composition)
             ","
             (Tactic.simpLemma [] [] `ContinuousMultilinearMap.comp_along_composition_apply)]
            "]"]
           [])
          [])
         (group (Tactic.congr "congr" [] []) [])
         (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `c)] []) [])
         (group (Tactic.congr "congr" [] []) [])
         (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `k)] []) [])
         (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
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
        ["["
         [(Tactic.simpLemma [] [] `left_inv)
          ","
          (Tactic.simpLemma [] [] `ContinuousMultilinearMap.neg_apply)
          ","
          (Tactic.simpLemma [] [] `neg_inj)
          ","
          (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
         "]"]
        [])
       [])
      (group
       (Tactic.convert
        "convert"
        []
        (Term.app
         (Term.proj
          (Term.proj
           (Term.app
            `sum_to_finset_eq_subtype
            [(Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder
                 [`c]
                 [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
               "=>"
               («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder
                 [`c]
                 [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
               "=>"
               (Term.app
                (Term.app
                 `ContinuousMultilinearMap.compAlongComposition
                 [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
                  `c
                  (Term.app `p.left_inv [`i `c.length])])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder
                     [`j]
                     [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
                   "=>"
                   (Term.app
                    `p
                    [(numLit "1")
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                       "=>"
                       (Term.app `v [`j])))])))])))])
           "."
           `symm)
          "."
          `trans)
         [(Term.hole "_")])
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma [] [] `comp_continuous_linear_map_apply_composition)
          ","
          (Tactic.simpLemma [] [] `ContinuousMultilinearMap.comp_along_composition_apply)]
         "]"]
        [])
       [])
      (group (Tactic.congr "congr" [] []) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `c)] []) [])
      (group (Tactic.congr "congr" [] []) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `k)] []) [])
      (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `k)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `c)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `comp_continuous_linear_map_apply_composition)
     ","
     (Tactic.simpLemma [] [] `ContinuousMultilinearMap.comp_along_composition_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMultilinearMap.comp_along_composition_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_continuous_linear_map_apply_composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.convert
   "convert"
   []
   (Term.app
    (Term.proj
     (Term.proj
      (Term.app
       `sum_to_finset_eq_subtype
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder
            [`c]
            [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
          "=>"
          («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder
            [`c]
            [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
          "=>"
          (Term.app
           (Term.app
            `ContinuousMultilinearMap.compAlongComposition
            [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
             `c
             (Term.app `p.left_inv [`i `c.length])])
           [(Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder
                [`j]
                [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
              "=>"
              (Term.app
               `p
               [(numLit "1")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                  "=>"
                  (Term.app `v [`j])))])))])))])
      "."
      `symm)
     "."
     `trans)
    [(Term.hole "_")])
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.convert', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.proj
     (Term.app
      `sum_to_finset_eq_subtype
      [(Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder
           [`c]
           [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
         "=>"
         («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder
           [`c]
           [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
         "=>"
         (Term.app
          (Term.app
           `ContinuousMultilinearMap.compAlongComposition
           [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
            `c
            (Term.app `p.left_inv [`i `c.length])])
          [(Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder
               [`j]
               [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
             "=>"
             (Term.app
              `p
              [(numLit "1")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                 "=>"
                 (Term.app `v [`j])))])))])))])
     "."
     `symm)
    "."
    `trans)
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
  (Term.proj
   (Term.proj
    (Term.app
     `sum_to_finset_eq_subtype
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder
          [`c]
          [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
        "=>"
        («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder
          [`c]
          [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
        "=>"
        (Term.app
         (Term.app
          `ContinuousMultilinearMap.compAlongComposition
          [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
           `c
           (Term.app `p.left_inv [`i `c.length])])
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder
              [`j]
              [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
            "=>"
            (Term.app
             `p
             [(numLit "1")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                "=>"
                (Term.app `v [`j])))])))])))])
    "."
    `symm)
   "."
   `trans)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj
   (Term.app
    `sum_to_finset_eq_subtype
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder
         [`c]
         [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
       "=>"
       («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder
         [`c]
         [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
       "=>"
       (Term.app
        (Term.app
         `ContinuousMultilinearMap.compAlongComposition
         [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
          `c
          (Term.app `p.left_inv [`i `c.length])])
        [(Term.fun
          "fun"
          (Term.basicFun
           [(Term.simpleBinder
             [`j]
             [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
           "=>"
           (Term.app
            `p
            [(numLit "1")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
               "=>"
               (Term.app `v [`j])))])))])))])
   "."
   `symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app
   `sum_to_finset_eq_subtype
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder
        [`c]
        [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
      "=>"
      («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder
        [`c]
        [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
      "=>"
      (Term.app
       (Term.app
        `ContinuousMultilinearMap.compAlongComposition
        [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
         `c
         (Term.app `p.left_inv [`i `c.length])])
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`j] [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
          "=>"
          (Term.app
           `p
           [(numLit "1")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
              "=>"
              (Term.app `v [`j])))])))])))])
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
    [(Term.simpleBinder
      [`c]
      [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
    "=>"
    (Term.app
     (Term.app
      `ContinuousMultilinearMap.compAlongComposition
      [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
       `c
       (Term.app `p.left_inv [`i `c.length])])
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`j] [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
        "=>"
        (Term.app
         `p
         [(numLit "1")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
            "=>"
            (Term.app `v [`j])))])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.app
    `ContinuousMultilinearMap.compAlongComposition
    [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
     `c
     (Term.app `p.left_inv [`i `c.length])])
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`j] [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
      "=>"
      (Term.app
       `p
       [(numLit "1")
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
          "=>"
          (Term.app `v [`j])))])))])
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
    [(Term.simpleBinder [`j] [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
    "=>"
    (Term.app
     `p
     [(numLit "1")
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
        "=>"
        (Term.app `v [`j])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p
   [(numLit "1")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
      "=>"
      (Term.app `v [`j])))])
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
    [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
    "=>"
    (Term.app `v [`j])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `v [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `v
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app
   `ContinuousMultilinearMap.compAlongComposition
   [(Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
    `c
    (Term.app `p.left_inv [`i `c.length])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.left_inv [`i `c.length])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.left_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.left_inv [`i `c.length]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.comp_continuous_linear_map [(Init.Coe.«term↑_» "↑" `i.symm)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↑_» "↑" `i.symm)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↑_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i.symm
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 999 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 999, (some 999, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Coe.«term↑_» "↑" `i.symm) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.comp_continuous_linear_map
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `p.comp_continuous_linear_map [(Term.paren "(" [(Init.Coe.«term↑_» "↑" `i.symm) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ContinuousMultilinearMap.compAlongComposition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `ContinuousMultilinearMap.compAlongComposition
   [(Term.paren
     "("
     [(Term.app `p.comp_continuous_linear_map [(Term.paren "(" [(Init.Coe.«term↑_» "↑" `i.symm) []] ")")]) []]
     ")")
    `c
    (Term.paren "(" [(Term.app `p.left_inv [`i `c.length]) []] ")")])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder
      [`c]
      [(Term.typeSpec ":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
    "=>"
    («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder
      [`c]
      [(Term.typeSpec
        ":"
        (Term.app `Composition [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")]))])]
    "=>"
    («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_to_finset_eq_subtype
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `sum_to_finset_eq_subtype
   [(Term.paren
     "("
     [(Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder
          [`c]
          [(Term.typeSpec
            ":"
            (Term.app `Composition [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")]))])]
        "=>"
        («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))
      []]
     ")")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder
        [`c]
        [(Term.typeSpec
          ":"
          (Term.app `Composition [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")]))])]
      "=>"
      (Term.app
       (Term.paren
        "("
        [(Term.app
          `ContinuousMultilinearMap.compAlongComposition
          [(Term.paren
            "("
            [(Term.app `p.comp_continuous_linear_map [(Term.paren "(" [(Init.Coe.«term↑_» "↑" `i.symm) []] ")")]) []]
            ")")
           `c
           (Term.paren "(" [(Term.app `p.left_inv [`i `c.length]) []] ")")])
         []]
        ")")
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder
            [`j]
            [(Term.typeSpec
              ":"
              (Term.app `Finₓ [(Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")]))])]
          "=>"
          (Term.app
           `p
           [(numLit "1")
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [`k] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
              "=>"
              (Term.app `v [`j])))])))])))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma [] [] `left_inv)
     ","
     (Tactic.simpLemma [] [] `ContinuousMultilinearMap.neg_apply)
     ","
     (Tactic.simpLemma [] [] `neg_inj)
     ","
     (Tactic.simpLemma [] [] `ContinuousMultilinearMap.sum_apply)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMultilinearMap.sum_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `neg_inj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ContinuousMultilinearMap.neg_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `left_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `p.left_inv
    [`i
     (Init.Logic.«term_+_» `n "+" (numLit "2"))
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`j] [(Term.typeSpec ":" (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]))])]
       "=>"
       (Term.app
        `p
        [(numLit "1") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `v [`j])))])))])
   "="
   («term-_»
    "-"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders
      (Lean.unbracketedExplicitBinders
       [(Lean.binderIdent `c)]
       [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
     " in "
     (Term.proj
      (Set.«term{_|_}»
       "{"
       (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
       "|"
       («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
       "}")
      "."
      `toFinset)
     ", "
     (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_»
   "-"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `c)]
      [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
    " in "
    (Term.proj
     (Set.«term{_|_}»
      "{"
      (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
      "|"
      («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
      "}")
     "."
     `toFinset)
    ", "
    (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `c)]
     [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
   " in "
   (Term.proj
    (Set.«term{_|_}»
     "{"
     (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
     "|"
     («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
     "}")
    "."
    `toFinset)
   ", "
   (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.app `p.left_inv [`i `c.length]) [(Term.app `p.apply_composition [`c `v])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.apply_composition [`c `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.apply_composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.apply_composition [`c `v]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `p.left_inv [`i `c.length])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.left_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.left_inv [`i `c.length]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
    "|"
    («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
    "}")
   "."
   `toFinset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}»
   "{"
   (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
   "|"
   («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» `c.length "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
    The left inverse to a formal multilinear series is indeed a left inverse, provided its linear
    term is invertible. -/
  theorem
    left_inv_comp
    ( p : FormalMultilinearSeries 𝕜 E F )
        ( i : E ≃L[ 𝕜 ] F )
        ( h : p 1 = continuousMultilinearCurryFin1 𝕜 E F . symm i )
      : left_inv p i . comp p = id 𝕜 E
    :=
      by
        ext n v
          cases n
          ·
            simp
              only
              [
                left_inv
                  ,
                  ContinuousMultilinearMap.zero_apply
                  ,
                  id_apply_ne_one
                  ,
                  Ne.def
                  ,
                  not_false_iff
                  ,
                  zero_ne_one
                  ,
                  comp_coeff_zero'
                ]
          cases n
          ·
            simp
              only
              [
                left_inv
                  ,
                  comp_coeff_one
                  ,
                  h
                  ,
                  id_apply_one
                  ,
                  ContinuousLinearEquiv.coe_apply
                  ,
                  ContinuousLinearEquiv.symm_apply_apply
                  ,
                  continuous_multilinear_curry_fin1_symm_apply
                ]
          have
            A
              :
                ( Finset.univ : Finset Composition n + 2 )
                  =
                  { c | Composition.length c < n + 2 } . toFinset ∪ { Composition.ones n + 2 }
              :=
              by
                refine' subset.antisymm fun c hc => _ subset_univ _
                  by_cases' h : c.length < n + 2
                  · simp [ h ]
                  · simp [ Composition.eq_ones_iff_le_length . 2 not_ltₓ . 1 h ]
          have
            B
              :
                Disjoint
                  ( { c | Composition.length c < n + 2 } : Set Composition n + 2 ) . toFinset { Composition.ones n + 2 }
              :=
              by simp
          have
            C
              :
                p.left_inv i Composition.ones n + 2 . length
                    fun
                      j : Finₓ Composition.ones n.succ.succ . length
                        =>
                        p 1 fun k => v Finₓ.castLe Composition.length_le _ j
                  =
                  p.left_inv i n + 2 fun j : Finₓ n + 2 => p 1 fun k => v j
              :=
              by
                apply FormalMultilinearSeries.congr _ Composition.ones_length _ fun j hj1 hj2 => _
                  exact FormalMultilinearSeries.congr _ rfl fun k hk1 hk2 => by congr
          have
            D
              :
                p.left_inv i n + 2 fun j : Finₓ n + 2 => p 1 fun k => v j
                  =
                  -
                    ∑
                      c : Composition n + 2
                      in
                      { c : Composition n + 2 | c.length < n + 2 } . toFinset
                      ,
                      p.left_inv i c.length p.apply_composition c v
              :=
              by
                simp
                    only
                    [ left_inv , ContinuousMultilinearMap.neg_apply , neg_inj , ContinuousMultilinearMap.sum_apply ]
                  convert
                    sum_to_finset_eq_subtype
                            fun c : Composition n + 2 => c.length < n + 2
                              fun
                                c : Composition n + 2
                                  =>
                                  ContinuousMultilinearMap.compAlongComposition
                                      p.comp_continuous_linear_map ↑ i.symm c p.left_inv i c.length
                                    fun j : Finₓ n + 2 => p 1 fun k : Finₓ 1 => v j
                          .
                          symm
                        .
                        trans
                      _
                  simp
                    only
                    [
                      comp_continuous_linear_map_apply_composition
                        ,
                        ContinuousMultilinearMap.comp_along_composition_apply
                      ]
                  congr
                  ext c
                  congr
                  ext k
                  simp [ h ]
          simp
            [
              FormalMultilinearSeries.comp
                ,
                show n + 2 ≠ 1 by decide
                ,
                A
                ,
                Finset.sum_union B
                ,
                apply_composition_ones
                ,
                C
                ,
                D
              ]

/-! ### The right inverse of a formal multilinear series -/


/--  The right inverse of a formal multilinear series, where the `n`-th term is defined inductively
in terms of the previous ones to make sure that `p ∘ (right_inv p i) = id`. For this, the linear
term `p₁` in `p` should be invertible. In the definition, `i` is a linear isomorphism that should
coincide with `p₁`, so that one can use its inverse in the construction. The definition does not
use that `i = p₁`, but proofs that the definition is well-behaved do.

The `n`-th term in `p ∘ q` is `∑ pₖ (q_{j₁}, ..., q_{jₖ})` over `j₁ + ... + jₖ = n`. In this
expression, `qₙ` appears only once, in `p₁ (qₙ)`. We adjust the definition of `qₙ` so that this
term compensates the rest of the sum, using `i⁻¹` as an inverse to `p₁`.

These formulas only make sense when the constant term `p₀` vanishes. The definition we give is
general, but it ignores the value of `p₀`.
-/
noncomputable def right_inv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : FormalMultilinearSeries 𝕜 F E
  | 0 => 0
  | 1 => (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm
  | n+2 =>
    let q : FormalMultilinearSeries 𝕜 F E := fun k => if h : k < n+2 then right_inv k else 0
    -(i.symm : F →L[𝕜] E).compContinuousMultilinearMap ((p.comp q) (n+2))

@[simp]
theorem right_inv_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) : p.right_inv i 0 = 0 := by
  rw [right_inv]

@[simp]
theorem right_inv_coeff_one (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.right_inv i 1 = (continuousMultilinearCurryFin1 𝕜 F E).symm i.symm := by
  rw [right_inv]

/--  The right inverse does not depend on the zeroth coefficient of a formal multilinear
series. -/
theorem right_inv_remove_zero (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F) :
    p.remove_zero.right_inv i = p.right_inv i := by
  ext1 n
  induction' n using Nat.strongRec' with n IH
  cases n
  ·
    simp
  cases n
  ·
    simp
  simp only [right_inv, neg_inj]
  unfold_coes
  congr 1
  rw
    [remove_zero_comp_of_pos _ _
      (show 0 < n+2by
        decide)]
  congr 1
  ext k
  by_cases' hk : k < n+2 <;> simp [hk, IH]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `comp_right_inv_aux1 [])
  (Command.declSig
   [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
    (Term.explicitBinder "(" [`hn] [":" («term_<_» (numLit "0") "<" `n)] [] ")")
    (Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`q] [":" (Term.app `FormalMultilinearSeries [`𝕜 `F `E])] [] ")")
    (Term.explicitBinder "(" [`v] [":" (Term.arrow (Term.app `Finₓ [`n]) "→" `F)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `p.comp [`q `n `v])
     "="
     (Init.Logic.«term_+_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders
        (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] [":" (Term.app `Composition [`n])]))
       " in "
       (Term.proj
        (Set.«term{_|_}»
         "{"
         (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [`n])])
         "|"
         («term_<_» (numLit "1") "<" `c.length)
         "}")
        "."
        `toFinset)
       ", "
       (Term.app `p [`c.length (Term.app `q.apply_composition [`c `v])]))
      "+"
      (Term.app
       `p
       [(numLit "1") (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`i] [])] "=>" (Term.app `q [`n `v])))])))))
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
           [`A []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.paren
               "("
               [`Finset.univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
               ")")
              "="
              (Init.Core.«term_∪_»
               (Term.proj
                (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                "."
                `toFinset)
               " ∪ "
               (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}"))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  `subset.antisymm
                  [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))
                   (Term.app `subset_univ [(Term.hole "_")])]))
                [])
               (group (Tactic.byCases' "by_cases'" [`h ":"] («term_<_» (numLit "1") "<" `c.length)) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
                [])
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
                        []
                        [(Term.typeSpec ":" («term_=_» `c.length "=" (numLit "1")))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.«tactic·._»
                              "·"
                              (Tactic.tacticSeq
                               (Tactic.tacticSeq1Indented
                                [(group
                                  (Tactic.refine'
                                   "refine'"
                                   (Term.proj
                                    (Term.app
                                     (Term.proj `eq_iff_le_not_lt "." (fieldIdx "2"))
                                     [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])
                                    "."
                                    `symm))
                                  [])
                                 (group (Tactic.exact "exact" (Term.app `c.length_pos_of_pos [`hn])) [])])))
                             [])]))))))
                     [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule ["←"] (Term.app `Composition.eq_single_iff_length [`hn]))]
                       "]")
                      [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                     [])
                    (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`B []]
           [(Term.typeSpec
             ":"
             (Term.app
              `Disjoint
              [(Term.proj
                (Term.paren
                 "("
                 [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                  [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
                 ")")
                "."
                `toFinset)
               (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}")]))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`C []]
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               `p
               [(Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
                (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])])
              "="
              (Term.app
               `p
               [(numLit "1")
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                  "=>"
                  (Term.app `q [`n `v])))])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group
                (Tactic.apply
                 "apply"
                 (Term.app
                  `p.congr
                  [(Term.app `Composition.single_length [`hn])
                   (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
                [])
               (group
                (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `apply_composition_single)] "]"] [])
                [])]))))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
           ","
           (Tactic.simpLemma [] [] `A)
           ","
           (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
           ","
           (Tactic.simpLemma [] [] `C)]
          "]"]
         [])
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
          [`A []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.paren
              "("
              [`Finset.univ [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
              ")")
             "="
             (Init.Core.«term_∪_»
              (Term.proj
               (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
               "."
               `toFinset)
              " ∪ "
              (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}"))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.refine'
                "refine'"
                (Term.app
                 `subset.antisymm
                 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))
                  (Term.app `subset_univ [(Term.hole "_")])]))
               [])
              (group (Tactic.byCases' "by_cases'" [`h ":"] («term_<_» (numLit "1") "<" `c.length)) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `h)] "]"] []) [])])))
               [])
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
                       []
                       [(Term.typeSpec ":" («term_=_» `c.length "=" (numLit "1")))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.«tactic·._»
                             "·"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(group
                                 (Tactic.refine'
                                  "refine'"
                                  (Term.proj
                                   (Term.app
                                    (Term.proj `eq_iff_le_not_lt "." (fieldIdx "2"))
                                    [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])
                                   "."
                                   `symm))
                                 [])
                                (group (Tactic.exact "exact" (Term.app `c.length_pos_of_pos [`hn])) [])])))
                            [])]))))))
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule ["←"] (Term.app `Composition.eq_single_iff_length [`hn]))]
                      "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
                    [])
                   (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `this)] "]"] []) [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`B []]
          [(Term.typeSpec
            ":"
            (Term.app
             `Disjoint
             [(Term.proj
               (Term.paren
                "("
                [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                 [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
                ")")
               "."
               `toFinset)
              (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}")]))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`C []]
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app
              `p
              [(Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
               (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])])
             "="
             (Term.app
              `p
              [(numLit "1")
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                 "=>"
                 (Term.app `q [`n `v])))])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (Tactic.apply
                "apply"
                (Term.app
                 `p.congr
                 [(Term.app `Composition.single_length [`hn])
                  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
               [])
              (group
               (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `apply_composition_single)] "]"] [])
               [])]))))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
          ","
          (Tactic.simpLemma [] [] `A)
          ","
          (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
          ","
          (Tactic.simpLemma [] [] `C)]
         "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `FormalMultilinearSeries.comp)
     ","
     (Tactic.simpLemma [] [] `A)
     ","
     (Tactic.simpLemma [] [] (Term.app `Finset.sum_union [`B]))
     ","
     (Tactic.simpLemma [] [] `C)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `C
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset.sum_union [`B])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset.sum_union
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `FormalMultilinearSeries.comp
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`C []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app
         `p
         [(Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
          (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])])
        "="
        (Term.app
         `p
         [(numLit "1")
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
            "=>"
            (Term.app `q [`n `v])))])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.apply
           "apply"
           (Term.app
            `p.congr
            [(Term.app `Composition.single_length [`hn])
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
          [])
         (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `apply_composition_single)] "]"] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.apply
        "apply"
        (Term.app
         `p.congr
         [(Term.app `Composition.single_length [`hn])
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `apply_composition_single)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `apply_composition_single)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `apply_composition_single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    `p.congr
    [(Term.app `Composition.single_length [`hn])
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p.congr
   [(Term.app `Composition.single_length [`hn])
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Composition.single_length [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.single_length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Composition.single_length [`hn]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    `p
    [(Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
     (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])])
   "="
   (Term.app
    `p
    [(numLit "1")
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
       "=>"
       (Term.app `q [`n `v])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p
   [(numLit "1")
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
      "=>"
      (Term.app `q [`n `v])))])
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
    [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
    "=>"
    (Term.app `q [`n `v])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `q [`n `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `q
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   `p
   [(Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
    (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `q.apply_composition [(Term.app `Composition.single [`n `hn]) `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Composition.single [`n `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Composition.single [`n `hn]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `q.apply_composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `q.apply_composition [(Term.paren "(" [(Term.app `Composition.single [`n `hn]) []] ")") `v]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.proj (Term.app `Composition.single [`n `hn]) "." `length)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Composition.single [`n `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Composition.single [`n `hn]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`B []]
     [(Term.typeSpec
       ":"
       (Term.app
        `Disjoint
        [(Term.proj
          (Term.paren
           "("
           [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
            [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
           ")")
          "."
          `toFinset)
         (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}")]))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Disjoint
   [(Term.proj
     (Term.paren
      "("
      [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
       [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
      ")")
     "."
     `toFinset)
    (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_}» "{" [(Term.app `Composition.single [`n `hn])] "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_}»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition.single [`n `hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.single
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.proj
   (Term.paren
    "("
    [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
     [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
    ")")
   "."
   `toFinset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.paren
   "("
   [(Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
    [(Term.typeAscription ":" (Term.app `Set [(Term.app `Composition [`n])]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Set [(Term.app `Composition [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Composition [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Set
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition.length [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem
  comp_right_inv_aux1
  { n : ℕ }
      ( hn : 0 < n )
      ( p : FormalMultilinearSeries 𝕜 E F )
      ( q : FormalMultilinearSeries 𝕜 F E )
      ( v : Finₓ n → F )
    :
      p.comp q n v
        =
        ∑ c : Composition n in { c : Composition n | 1 < c.length } . toFinset , p c.length q.apply_composition c v
          +
          p 1 fun i => q n v
  :=
    by
      have
          A
            :
              ( Finset.univ : Finset Composition n )
                =
                { c | 1 < Composition.length c } . toFinset ∪ { Composition.single n hn }
            :=
            by
              refine' subset.antisymm fun c hc => _ subset_univ _
                by_cases' h : 1 < c.length
                · simp [ h ]
                ·
                  have : c.length = 1 := by · refine' eq_iff_le_not_lt . 2 ⟨ _ , h ⟩ . symm exact c.length_pos_of_pos hn
                    rw [ ← Composition.eq_single_iff_length hn ] at this
                    simp [ this ]
        have
          B
            : Disjoint ( { c | 1 < Composition.length c } : Set Composition n ) . toFinset { Composition.single n hn }
            :=
            by simp
        have
          C
            :
              p Composition.single n hn . length q.apply_composition Composition.single n hn v
                =
                p 1 fun i : Finₓ 1 => q n v
            :=
            by apply p.congr Composition.single_length hn fun j hj1 hj2 => _ simp [ apply_composition_single ]
        simp [ FormalMultilinearSeries.comp , A , Finset.sum_union B , C ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `comp_right_inv_aux2 [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")
    (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder
     "("
     [`v]
     [":" (Term.arrow (Term.app `Finₓ [(Init.Logic.«term_+_» `n "+" (numLit "2"))]) "→" `F)]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `c)]
        [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
      " in "
      (Term.proj
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
        "|"
        («term_<_» (numLit "1") "<" `c.length)
        "}")
       "."
       `toFinset)
      ", "
      (Term.app
       `p
       [`c.length
        (Term.app
         `apply_composition
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
            "=>"
            (Term.app
             `ite
             [(«term_<_» `k "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
              (Term.app `p.right_inv [`i `k])
              (numLit "0")])))
          `c
          `v])]))
     "="
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders
       (Lean.unbracketedExplicitBinders
        [(Lean.binderIdent `c)]
        [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
      " in "
      (Term.proj
       (Set.«term{_|_}»
        "{"
        (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
        "|"
        («term_<_» (numLit "1") "<" `c.length)
        "}")
       "."
       `toFinset)
      ", "
      (Term.app `p [`c.length (Term.app (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition) [`c `v])])))))
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
           [`N []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
           ":="
           (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
        [])
       (group
        (Tactic.refine'
         "refine'"
         (Term.app
          `sum_congr
          [`rfl
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`c `hc] [])]
             "=>"
             (Term.app
              `p.congr
              [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])))]))
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
              [(Term.simpleBinder [`k] [])]
              ","
              («term_<_» (Term.app `c.blocks_fun [`k]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))]
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
                 ["[" [(Tactic.simpLemma [] [] `Set.mem_to_finset) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                 [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
                [])
               (group
                (Tactic.simp
                 "simp"
                 []
                 []
                 ["["
                  [(Tactic.simpLemma [] ["←"] (Term.app `Composition.ne_single_iff [`N]))
                   ","
                   (Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
                   ","
                   (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hc]))]
                  "]"]
                 [])
                [])]))))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["[" [(Tactic.simpLemma [] [] `apply_composition) "," (Tactic.simpLemma [] [] `this)] "]"]
         [])
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
          [`N []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
          ":="
          (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
       [])
      (group
       (Tactic.refine'
        "refine'"
        (Term.app
         `sum_congr
         [`rfl
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`c `hc] [])]
            "=>"
            (Term.app
             `p.congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])))]))
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
             [(Term.simpleBinder [`k] [])]
             ","
             («term_<_» (Term.app `c.blocks_fun [`k]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))]
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
                ["[" [(Tactic.simpLemma [] [] `Set.mem_to_finset) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
                [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
               [])
              (group
               (Tactic.simp
                "simp"
                []
                []
                ["["
                 [(Tactic.simpLemma [] ["←"] (Term.app `Composition.ne_single_iff [`N]))
                  ","
                  (Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
                  ","
                  (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hc]))]
                 "]"]
                [])
               [])]))))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["[" [(Tactic.simpLemma [] [] `apply_composition) "," (Tactic.simpLemma [] [] `this)] "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["[" [(Tactic.simpLemma [] [] `apply_composition) "," (Tactic.simpLemma [] [] `this)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `apply_composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
       (Term.forall
        "∀"
        [(Term.simpleBinder [`k] [])]
        ","
        («term_<_» (Term.app `c.blocks_fun [`k]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))))]
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
           ["[" [(Tactic.simpLemma [] [] `Set.mem_to_finset) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
          [])
         (group
          (Tactic.simp
           "simp"
           []
           []
           ["["
            [(Tactic.simpLemma [] ["←"] (Term.app `Composition.ne_single_iff [`N]))
             ","
             (Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
             ","
             (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hc]))]
            "]"]
           [])
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
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `Set.mem_to_finset) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
        [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] ["←"] (Term.app `Composition.ne_single_iff [`N]))
          ","
          (Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
          ","
          (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hc]))]
         "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] ["←"] (Term.app `Composition.ne_single_iff [`N]))
     ","
     (Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
     ","
     (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [`hc]))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ne_of_gtₓ [`hc])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `ne_of_gtₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Composition.eq_single_iff_length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition.ne_single_iff [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `N
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.ne_single_iff
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `Set.mem_to_finset) "," (Tactic.simpLemma [] [] `Set.mem_set_of_eq)] "]"]
   [(Tactic.location "at" (Tactic.locationHyp [`hc] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.location', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hc
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_set_of_eq
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Set.mem_to_finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`k] [])]
   ","
   («term_<_» (Term.app `c.blocks_fun [`k]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (Term.app `c.blocks_fun [`k]) "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app `c.blocks_fun [`k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `c.blocks_fun
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `sum_congr
    [`rfl
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`c `hc] [])]
       "=>"
       (Term.app
        `p.congr
        [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.refine'', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_congr
   [`rfl
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`c `hc] [])]
      "=>"
      (Term.app
       `p.congr
       [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])))])
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
    [(Term.simpleBinder [`c `hc] [])]
    "=>"
    (Term.app
     `p.congr
     [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `p.congr
   [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj1 `hj2] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.congr
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_congr
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
     [`N []]
     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.decide "decide")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'Lean.Parser.Tactic.decide.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `c)]
      [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
    " in "
    (Term.proj
     (Set.«term{_|_}»
      "{"
      (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
      "|"
      («term_<_» (numLit "1") "<" `c.length)
      "}")
     "."
     `toFinset)
    ", "
    (Term.app
     `p
     [`c.length
      (Term.app
       `apply_composition
       [(Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
          "=>"
          (Term.app
           `ite
           [(«term_<_» `k "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
            (Term.app `p.right_inv [`i `k])
            (numLit "0")])))
        `c
        `v])]))
   "="
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders
     (Lean.unbracketedExplicitBinders
      [(Lean.binderIdent `c)]
      [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
    " in "
    (Term.proj
     (Set.«term{_|_}»
      "{"
      (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
      "|"
      («term_<_» (numLit "1") "<" `c.length)
      "}")
     "."
     `toFinset)
    ", "
    (Term.app `p [`c.length (Term.app (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition) [`c `v])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders
    (Lean.unbracketedExplicitBinders
     [(Lean.binderIdent `c)]
     [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])]))
   " in "
   (Term.proj
    (Set.«term{_|_}»
     "{"
     (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
     "|"
     («term_<_» (numLit "1") "<" `c.length)
     "}")
    "."
    `toFinset)
   ", "
   (Term.app `p [`c.length (Term.app (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition) [`c `v])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`c.length (Term.app (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition) [`c `v])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition) [`c `v])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `v
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `p.right_inv [`i]) "." `applyComposition)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.right_inv [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.right_inv [`i]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app (Term.proj (Term.paren "(" [(Term.app `p.right_inv [`i]) []] ")") "." `applyComposition) [`c `v]) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj
   (Set.«term{_|_}»
    "{"
    (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
    "|"
    («term_<_» (numLit "1") "<" `c.length)
    "}")
   "."
   `toFinset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}»
   "{"
   (Mathlib.ExtendedBinder.extBinder `c [":" (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])])
   "|"
   («term_<_» (numLit "1") "<" `c.length)
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "1") "<" `c.length)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [(Init.Logic.«term_+_» `n "+" (numLit "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "2")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
theorem
  comp_right_inv_aux2
  ( p : FormalMultilinearSeries 𝕜 E F ) ( i : E ≃L[ 𝕜 ] F ) ( n : ℕ ) ( v : Finₓ n + 2 → F )
    :
      ∑
          c : Composition n + 2
          in
          { c : Composition n + 2 | 1 < c.length } . toFinset
          ,
          p c.length apply_composition fun k : ℕ => ite k < n + 2 p.right_inv i k 0 c v
        =
        ∑
          c : Composition n + 2
          in
          { c : Composition n + 2 | 1 < c.length } . toFinset
          ,
          p c.length p.right_inv i . applyComposition c v
  :=
    by
      have N : 0 < n + 2 := by decide
        refine' sum_congr rfl fun c hc => p.congr rfl fun j hj1 hj2 => _
        have
          : ∀ k , c.blocks_fun k < n + 2
            :=
            by
              simp only [ Set.mem_to_finset , Set.mem_set_of_eq ] at hc
                simp [ ← Composition.ne_single_iff N , Composition.eq_single_iff_length , ne_of_gtₓ hc ]
        simp [ apply_composition , this ]

/--  The right inverse to a formal multilinear series is indeed a right inverse, provided its linear
term is invertible and its constant term vanishes. -/
theorem comp_right_inv (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) (h0 : p 0 = 0) : p.comp (right_inv p i) = id 𝕜 F := by
  ext n v
  cases n
  ·
    simp only [h0, ContinuousMultilinearMap.zero_apply, id_apply_ne_one, Ne.def, not_false_iff, zero_ne_one,
      comp_coeff_zero']
  cases n
  ·
    simp only [comp_coeff_one, h, right_inv, ContinuousLinearEquiv.apply_symm_apply, id_apply_one,
      ContinuousLinearEquiv.coe_apply, continuous_multilinear_curry_fin1_symm_apply]
  have N : 0 < n+2 := by
    decide
  simp [comp_right_inv_aux1 N, h, right_inv, lt_irreflₓ n,
    show (n+2) ≠ 1by
      decide,
    ← sub_eq_add_neg, sub_eq_zero, comp_right_inv_aux2]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `right_inv_coeff [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")
    (Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder "(" [`hn] [":" («term_≤_» (numLit "2") "≤" `n)] [] ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `p.right_inv [`i `n])
     "="
     («term-_»
      "-"
      (Term.app
       (Term.proj
        (Term.paren
         "("
         [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
         ")")
        "."
        `compContinuousMultilinearMap)
       [(Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
         " in "
         (Term.paren
          "("
          [(Term.proj
            (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
            "."
            `toFinset)
           [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
          ")")
         ", "
         (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `zero_lt_two.not_le [`hn])])) [])])))
        [])
       (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `one_lt_two.not_le [`hn])])) [])])))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         ["only"]
         ["[" [(Tactic.simpLemma [] [] `right_inv) "," (Tactic.simpLemma [] [] `neg_inj)] "]"]
         [])
        [])
       (group (Tactic.congr "congr" [(numLit "1")] []) [])
       (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `v)] []) [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`N []]
           [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
           ":="
           (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           []
           [(Term.typeSpec
             ":"
             («term_=_»
              (Term.app
               (Term.app `p [(numLit "1")])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                  "=>"
                  (numLit "0")))])
              "="
              (numLit "0")))]
           ":="
           (Term.app `ContinuousMultilinearMap.map_zero [(Term.hole "_")]))))
        [])
       (group
        (Tactic.simp
         "simp"
         []
         []
         ["["
          [(Tactic.simpLemma [] [] (Term.app `comp_right_inv_aux1 [`N]))
           ","
           (Tactic.simpLemma [] [] (Term.app `lt_irreflₓ [`n]))
           ","
           (Tactic.simpLemma [] [] `this)
           ","
           (Tactic.simpLemma [] [] `comp_right_inv_aux2)]
          "]"]
         [])
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
     [(group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `zero_lt_two.not_le [`hn])])) [])])))
       [])
      (group (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] []) [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `one_lt_two.not_le [`hn])])) [])])))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["[" [(Tactic.simpLemma [] [] `right_inv) "," (Tactic.simpLemma [] [] `neg_inj)] "]"]
        [])
       [])
      (group (Tactic.congr "congr" [(numLit "1")] []) [])
      (group (Tactic.ext "ext" [(Tactic.rcasesPat.one `v)] []) [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`N []]
          [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
          ":="
          (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            («term_=_»
             (Term.app
              (Term.app `p [(numLit "1")])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
                 "=>"
                 (numLit "0")))])
             "="
             (numLit "0")))]
          ":="
          (Term.app `ContinuousMultilinearMap.map_zero [(Term.hole "_")]))))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] (Term.app `comp_right_inv_aux1 [`N]))
          ","
          (Tactic.simpLemma [] [] (Term.app `lt_irreflₓ [`n]))
          ","
          (Tactic.simpLemma [] [] `this)
          ","
          (Tactic.simpLemma [] [] `comp_right_inv_aux2)]
         "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] (Term.app `comp_right_inv_aux1 [`N]))
     ","
     (Tactic.simpLemma [] [] (Term.app `lt_irreflₓ [`n]))
     ","
     (Tactic.simpLemma [] [] `this)
     ","
     (Tactic.simpLemma [] [] `comp_right_inv_aux2)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `comp_right_inv_aux2
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `this
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `lt_irreflₓ [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `lt_irreflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `comp_right_inv_aux1 [`N])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `N
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `comp_right_inv_aux1
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
       («term_=_»
        (Term.app
         (Term.app `p [(numLit "1")])
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
            "=>"
            (numLit "0")))])
        "="
        (numLit "0")))]
     ":="
     (Term.app `ContinuousMultilinearMap.map_zero [(Term.hole "_")]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `ContinuousMultilinearMap.map_zero [(Term.hole "_")])
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
  `ContinuousMultilinearMap.map_zero
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app
    (Term.app `p [(numLit "1")])
    [(Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
       "=>"
       (numLit "0")))])
   "="
   (numLit "0"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Term.app
   (Term.app `p [(numLit "1")])
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
      "=>"
      (numLit "0")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])] "=>" (numLit "0")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finₓ [(numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `p [(numLit "1")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p [(numLit "1")]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.paren "(" [(Term.app `p [(numLit "1")]) []] ")")
   [(Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [(numLit "1")]))])]
      "=>"
      (numLit "0")))])
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`N []]
     [(Term.typeSpec ":" («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2"))))]
     ":="
     (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.decide "decide")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'Lean.Parser.Tactic.decide.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "0") "<" (Init.Logic.«term_+_» `n "+" (numLit "2")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "2"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "2")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.ext "ext" [(Tactic.rcasesPat.one `v)] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.ext', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rcasesPat.one', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.congr "congr" [(numLit "1")] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.congr', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `right_inv) "," (Tactic.simpLemma [] [] `neg_inj)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `neg_inj
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `one_lt_two.not_le [`hn])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `False.elim [(Term.app `one_lt_two.not_le [`hn])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `False.elim [(Term.app `one_lt_two.not_le [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `one_lt_two.not_le [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `one_lt_two.not_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `one_lt_two.not_le [`hn]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `False.elim
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.«tactic·._»
   "·"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Tactic.exact "exact" (Term.app `False.elim [(Term.app `zero_lt_two.not_le [`hn])])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `False.elim [(Term.app `zero_lt_two.not_le [`hn])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `False.elim [(Term.app `zero_lt_two.not_le [`hn])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `zero_lt_two.not_le [`hn])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hn
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `zero_lt_two.not_le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `zero_lt_two.not_le [`hn]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `False.elim
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.cases "cases" [(Tactic.casesTarget [] `n)] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.cases', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.casesTarget', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declSig', expected 'Lean.Parser.Command.declSig.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_»
   (Term.app `p.right_inv [`i `n])
   "="
   («term-_»
    "-"
    (Term.app
     (Term.proj
      (Term.paren
       "("
       [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
       ")")
      "."
      `compContinuousMultilinearMap)
     [(Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
       " in "
       (Term.paren
        "("
        [(Term.proj
          (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
          "."
          `toFinset)
         [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
        ")")
       ", "
       (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term-_»
   "-"
   (Term.app
    (Term.proj
     (Term.paren
      "("
      [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
      ")")
     "."
     `compContinuousMultilinearMap)
    [(Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
      " in "
      (Term.paren
       "("
       [(Term.proj
         (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
         "."
         `toFinset)
        [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
       ")")
      ", "
      (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term-_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.proj
    (Term.paren
     "("
     [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
     ")")
    "."
    `compContinuousMultilinearMap)
   [(Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
     " in "
     (Term.paren
      "("
      [(Term.proj
        (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
        "."
        `toFinset)
       [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
      ")")
     ", "
     (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
   " in "
   (Term.paren
    "("
    [(Term.proj
      (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
      "."
      `toFinset)
     [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
    ")")
   ", "
   (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `p.right_inv [`i])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `p.right_inv [`i]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.comp_along_composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.paren
   "("
   [(Term.proj
     (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
     "."
     `toFinset)
    [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`n])]))]]
   ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.paren', expected 'Lean.Parser.Term.paren.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'null', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.tupleTail'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeAscription', expected 'Lean.Parser.Term.typeAscription.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Finset [(Term.app `Composition [`n])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition [`n])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Composition [`n]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  (Term.proj
   (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
   "."
   `toFinset)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_<_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Composition.length [`c])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `c
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Composition.length
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Mathlib.ExtendedBinder.extBinder'
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
theorem
  right_inv_coeff
  ( p : FormalMultilinearSeries 𝕜 E F ) ( i : E ≃L[ 𝕜 ] F ) ( n : ℕ ) ( hn : 2 ≤ n )
    :
      p.right_inv i n
        =
        -
          ( i.symm : F →L[ 𝕜 ] E ) . compContinuousMultilinearMap
            ∑
              c
              in
              ( { c | 1 < Composition.length c } . toFinset : Finset Composition n )
              ,
              p.comp_along_composition p.right_inv i c
  :=
    by
      cases n
        · exact False.elim zero_lt_two.not_le hn
        cases n
        · exact False.elim one_lt_two.not_le hn
        simp only [ right_inv , neg_inj ]
        congr 1
        ext v
        have N : 0 < n + 2 := by decide
        have : p 1 fun i : Finₓ 1 => 0 = 0 := ContinuousMultilinearMap.map_zero _
        simp [ comp_right_inv_aux1 N , lt_irreflₓ n , this , comp_right_inv_aux2 ]

/-! ### Coincidence of the left and the right inverse -/


private theorem left_inv_eq_right_inv_aux (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) (h0 : p 0 = 0) : left_inv p i = right_inv p i :=
  calc left_inv p i = (left_inv p i).comp (id 𝕜 F) := by
    simp
    _ = (left_inv p i).comp (p.comp (right_inv p i)) := by
    rw [comp_right_inv p i h h0]
    _ = ((left_inv p i).comp p).comp (right_inv p i) := by
    rw [comp_assoc]
    _ = (id 𝕜 E).comp (right_inv p i) := by
    rw [left_inv_comp p i h]
    _ = right_inv p i := by
    simp
    

/--  The left inverse and the right inverse of a formal multilinear series coincide. This is not at
all obvious from their definition, but it follows from uniqueness of inverses (which comes from the
fact that composition is associative on formal multilinear series). -/
theorem left_inv_eq_right_invₓ (p : FormalMultilinearSeries 𝕜 E F) (i : E ≃L[𝕜] F)
    (h : p 1 = (continuousMultilinearCurryFin1 𝕜 E F).symm i) : left_inv p i = right_inv p i :=
  calc left_inv p i = left_inv p.remove_zero i := by
    rw [left_inv_remove_zero]
    _ = right_inv p.remove_zero i := by
    apply left_inv_eq_right_inv_aux <;> simp [h]
    _ = right_inv p i := by
    rw [right_inv_remove_zero]
    

/-!
### Convergence of the inverse of a power series

Assume that `p` is a convergent multilinear series, and let `q` be its (left or right) inverse.
Using the left-inverse formula gives
$$
q_n = - (p_1)^{-n} \sum_{k=0}^{n-1} \sum_{i_1 + \dotsc + i_k = n} q_k (p_{i_1}, \dotsc, p_{i_k}).
$$
Assume for simplicity that we are in dimension `1` and `p₁ = 1`. In the formula for `qₙ`, the term
`q_{n-1}` appears with a multiplicity of `n-1` (choosing the index `i_j` for which `i_j = 2` while
all the other indices are equal to `1`), which indicates that `qₙ` might grow like `n!`. This is
bad for summability properties.

It turns out that the right-inverse formula is better behaved, and should instead be used for this
kind of estimate. It reads
$$
q_n = - (p_1)^{-1} \sum_{k=2}^n \sum_{i_1 + \dotsc + i_k = n} p_k (q_{i_1}, \dotsc, q_{i_k}).
$$
Here, `q_{n-1}` can only appear in the term with `k = 2`, and it only appears twice, so there is
hope this formula can lead to an at most geometric behavior.

Let `Qₙ = ∥qₙ∥`. Bounding `∥pₖ∥` with `C r^k` gives an inequality
$$
Q_n ≤ C' \sum_{k=2}^n r^k \sum_{i_1 + \dotsc + i_k = n} Q_{i_1} \dotsm Q_{i_k}.
$$

This formula is not enough to prove by naive induction on `n` a bound of the form `Qₙ ≤ D R^n`.
However, assuming that the inequality above were an equality, one could get a formula for the
generating series of the `Qₙ`:

$$
\begin{align}
Q(z) & := \sum Q_n z^n = Q_1 z + C' \sum_{2 \leq k \leq n} \sum_{i_1 + \dotsc + i_k = n}
  (r z^{i_1} Q_{i_1}) \dotsm (r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (\sum_{i_1 \geq 1} r z^{i_1} Q_{i_1})
  \dotsm (\sum_{i_k \geq 1} r z^{i_k} Q_{i_k})
\\ & = Q_1 z + C' \sum_{k = 2}^\infty (r Q(z))^k
= Q_1 z + C' (r Q(z))^2 / (1 - r Q(z)).
\end{align}
$$

One can solve this formula explicitly. The solution is analytic in a neighborhood of `0` in `ℂ`,
hence its coefficients grow at most geometrically (by a contour integral argument), and therefore
the original `Qₙ`, which are bounded by these ones, are also at most geometric.

This classical argument is not really satisfactory, as it requires an a priori bound on a complex
analytic function. Another option would be to compute explicitly its terms (with binomial
coefficients) to obtain an explicit geometric bound, but this would be very painful.

Instead, we will use the above intuition, but in a slightly different form, with finite sums and an
induction. I learnt this trick in [pöschel2017siegelsternberg]. Let
$S_n = \sum_{k=1}^n Q_k a^k$ (where `a` is a positive real parameter to be chosen suitably small).
The above computation but with finite sums shows that

$$
S_n \leq Q_1 a + C' \sum_{k=2}^n (r S_{n-1})^k.
$$

In particular, $S_n \leq Q_1 a + C' (r S_{n-1})^2 / (1- r S_{n-1})$.
Assume that $S_{n-1} \leq K a$, where `K > Q₁` is fixed and `a` is small enough so that
`r K a ≤ 1/2` (to control the denominator). Then this equation gives a bound
$S_n \leq Q_1 a + 2 C' r^2 K^2 a^2$.
If `a` is small enough, this is bounded by `K a` as the second term is quadratic in `a`, and
therefore negligible.

By induction, we deduce `Sₙ ≤ K a` for all `n`, which gives in particular the fact that `aⁿ Qₙ`
remains bounded.
-/


/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " First technical lemma to control the growth of coefficients of the inverse. Bound the explicit\nexpression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,\nin a general abstract setup. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `radius_right_inv_pos_of_radius_pos_aux1 [])
  (Command.declSig
   [(Term.explicitBinder "(" [`n] [":" (termℕ "ℕ")] [] ")")
    (Term.explicitBinder "(" [`p] [":" (Term.arrow (termℕ "ℕ") "→" (Data.Real.Basic.termℝ "ℝ"))] [] ")")
    (Term.explicitBinder
     "("
     [`hp]
     [":" (Term.forall "∀" [(Term.simpleBinder [`k] [])] "," («term_≤_» (numLit "0") "≤" (Term.app `p [`k])))]
     []
     ")")
    (Term.implicitBinder "{" [`r `a] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`hr] [":" («term_≤_» (numLit "0") "≤" `r)] [] ")")
    (Term.explicitBinder "(" [`ha] [":" («term_≤_» (numLit "0") "≤" `a)] [] ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
      " in "
      (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" `k)
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
        " in "
        (Term.paren
         "("
         [(Term.proj
           (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
           "."
           `toFinset)
          [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
         ")")
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `r "^" `c.length)
         "*"
         (Algebra.BigOperators.Basic.«term∏_,_»
          "∏"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
          ", "
          (Term.app `p [(Term.app `c.blocks_fun [`j])]))))))
     "≤"
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      " in "
      (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `r "^" `j)
       "*"
       («term_^_»
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "1") `n])
         ", "
         (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `k) "*" (Term.app `p [`k])))
        "^"
        `j))))))
  (Command.declValSimple
   ":="
   (calc
    "calc"
    [(calcStep
      («term_=_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `k)
         "*"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
          " in "
          (Term.paren
           "("
           [(Term.proj
             (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
             "."
             `toFinset)
            [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
           ")")
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `r "^" `c.length)
           "*"
           (Algebra.BigOperators.Basic.«term∏_,_»
            "∏"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
            ", "
            (Term.app `p [(Term.app `c.blocks_fun [`j])]))))))
       "="
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
         " in "
         (Term.paren
          "("
          [(Term.proj
            (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
            "."
            `toFinset)
           [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
          ")")
         ", "
         (Algebra.BigOperators.Basic.«term∏_,_»
          "∏"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           `r
           "*"
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `a "^" (Term.app `c.blocks_fun [`j]))
            "*"
            (Term.app `p [(Term.app `c.blocks_fun [`j])])))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") []) [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))]))
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))]))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `prod_mul_distrib)
              ","
              (Tactic.rwRule [] `prod_mul_distrib)
              ","
              (Tactic.rwRule [] `prod_pow_eq_pow_sum)
              ","
              (Tactic.rwRule [] `Composition.sum_blocks_fun)
              ","
              (Tactic.rwRule [] `prod_const)
              ","
              (Tactic.rwRule [] `card_fin)]
             "]")
            [])
           [])
          (group (Tactic.Ring.tacticRing "ring") [])]))))
     (calcStep
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
        " in "
        (Term.app `comp_partial_sum_target [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
        ", "
        (Algebra.BigOperators.Basic.«term∏_,_»
         "∏"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `j)]
           [":" (Term.app `Finₓ [(Term.proj (Term.proj `d "." (fieldIdx "2")) "." `length)])]))
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          `r
          "*"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" (Term.app (Term.proj (Term.proj `d "." (fieldIdx "2")) "." `blocksFun) [`j]))
           "*"
           (Term.app `p [(Term.app (Term.proj (Term.proj `d "." (fieldIdx "2")) "." `blocksFun) [`j])]))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sum_sigma')] "]") []) [])
          (group
           (Tactic.refine'
            "refine'"
            (Term.app
             `sum_le_sum_of_subset_of_nonneg
             [(Term.hole "_")
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`x `hx1 `hx2] [])]
                "=>"
                (Term.app
                 `prod_nonneg
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`j `hj] [])]
                    "=>"
                    (Term.app
                     `mul_nonneg
                     [`hr
                      (Term.app
                       `mul_nonneg
                       [(Term.app `pow_nonneg [`ha (Term.hole "_")]) (Term.app `hp [(Term.hole "_")])])])))])))]))
           [])
          (group
           (Tactic.rintro
            "rintro"
            [(Tactic.rintroPat.one
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])]
               "⟩"))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))]
            [])
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Set.mem_to_finset)
              ","
              (Tactic.simpLemma [] [] `mem_Ico)
              ","
              (Tactic.simpLemma [] [] `mem_sigma)
              ","
              (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
             "]"]
            [(Tactic.location "at" (Tactic.locationHyp [`hd] []))])
           [])
          (group
           (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_comp_partial_sum_target_iff)] "]"] [])
           [])
          (group
           (Tactic.refine'
            "refine'"
            (Term.anonymousCtor
             "⟨"
             [(Term.proj `hd "." (fieldIdx "2"))
              ","
              (Term.app `c.length_le.trans_lt [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "2"))])
              ","
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.hole "_")))]
             "⟩"))
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              []
              [(Term.typeSpec
                ":"
                («term_≠_»
                 `c
                 "≠"
                 (Term.app
                  `Composition.single
                  [`k
                   (Term.app
                    `zero_lt_two.trans_le
                    [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "1"))])])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group
                   (Tactic.simp
                    "simp"
                    []
                    []
                    ["["
                     [(Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
                      ","
                      (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [(Term.proj `hd "." (fieldIdx "2"))]))]
                     "]"]
                    [])
                   [])]))))))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Composition.ne_single_iff)] "]")
            [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
           [])
          (group
           (Tactic.exact
            "exact"
            (Term.app
             (Term.proj (Term.app `this [`j]) "." `trans_le)
             [(Term.app `nat.lt_succ_iff.mp [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "2"))])]))
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
        " in "
        (Term.app `comp_partial_sum_source [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
        ", "
        (Algebra.BigOperators.Basic.«term∏_,_»
         "∏"
         (Lean.explicitBinders
          (Lean.unbracketedExplicitBinders
           [(Lean.binderIdent `j)]
           [":" (Term.app `Finₓ [(Term.proj `e "." (fieldIdx "1"))])]))
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          `r
          "*"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" (Term.app (Term.proj `e "." (fieldIdx "2")) [`j]))
           "*"
           (Term.app `p [(Term.app (Term.proj `e "." (fieldIdx "2")) [`j])]))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.symm "symm") [])
          (group (Tactic.apply "apply" `comp_change_of_variables_sum) [])
          (group
           (Tactic.rintro
            "rintro"
            [(Tactic.rintroPat.one
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `blocks_fun)]) [])]
               "⟩"))
             (Tactic.rintroPat.one (Tactic.rcasesPat.one `H))]
            [])
           [])
          (group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`K []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.proj
                  (Term.proj
                   (Term.app
                    `comp_change_of_variables
                    [(numLit "2")
                     (Init.Logic.«term_+_» `n "+" (numLit "1"))
                     `n
                     (Term.anonymousCtor "⟨" [`k "," `blocks_fun] "⟩")
                     `H])
                   "."
                   `snd)
                  "."
                  `length)
                 "="
                 `k))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
           [])
          (group
           (Tactic.«tactic_<;>_»
            (Tactic.congr "congr" [(numLit "2")] [])
            "<;>"
            (Tactic.tacticTry_
             "try"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `K)] "]") []) [])]))))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finₓ.heq_fun_iff [`K.symm]))] "]")
            [])
           [])
          (group (Tactic.intro "intro" [`j]) [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_change_of_variables_blocks_fun)] "]")
            [])
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `r "^" `j)
         "*"
         («term_^_»
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
           " in "
           (Term.app `Ico [(numLit "1") `n])
           ", "
           (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `k) "*" (Term.app `p [`k])))
          "^"
          `j))))
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
             [(Tactic.rwRule [] `comp_partial_sum_source)
              ","
              (Tactic.rwRule
               ["←"]
               (Term.app
                `sum_sigma'
                [(Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                   "=>"
                   (Term.paren
                    "("
                    [(Term.app
                      `Fintype.piFinset
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])]
                         "=>"
                         (Term.app `Ico [(numLit "1") `n])))])
                     [(Term.typeAscription
                       ":"
                       (Term.app `Finset [(Term.arrow (Term.app `Finₓ [`k]) "→" (termℕ "ℕ"))]))]]
                    ")")))
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`n `e] [])]
                   "=>"
                   (Algebra.BigOperators.Basic.«term∏_,_»
                    "∏"
                    (Lean.explicitBinders
                     (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
                    ", "
                    (Finset.Data.Finset.Fold.«term_*_»
                     `r
                     "*"
                     (Finset.Data.Finset.Fold.«term_*_»
                      («term_^_» `a "^" (Term.app `e [`j]))
                      "*"
                      (Term.app `p [(Term.app `e [`j])]))))))]))]
             "]")
            [])
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               ["←"]
               (Term.app
                (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
                [(Data.Real.Basic.termℝ "ℝ")
                 (Term.app `Finₓ [`j])
                 (Term.hole "_")
                 (Term.hole "_")
                 (Data.Real.Basic.termℝ "ℝ")]))]
             "]"]
            [])
           [])
          (group
           (Tactic.simp
            "simp"
            []
            ["only"]
            ["["
             [(Tactic.simpLemma
               []
               ["←"]
               (Term.app
                `MultilinearMap.map_sum_finset
                [(Term.app
                  `MultilinearMap.mkPiAlgebra
                  [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
                 (Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                   "=>"
                   (Finset.Data.Finset.Fold.«term_*_»
                    `r
                    "*"
                    (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))]))]
             "]"]
            [])
           [])
          (group
           (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `MultilinearMap.mk_pi_algebra_apply)] "]"] [])
           [])
          (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
          (group
           (Tactic.simp
            "simp"
            []
            []
            ["["
             [(Tactic.simpLemma [] [] `prod_const)
              ","
              (Tactic.simpLemma [] ["←"] `mul_sum)
              ","
              (Tactic.simpLemma [] [] `mul_powₓ)]
             "]"]
            [])
           [])]))))])
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
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_^_» `a "^" `k)
        "*"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
         " in "
         (Term.paren
          "("
          [(Term.proj
            (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
            "."
            `toFinset)
           [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
          ")")
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `r "^" `c.length)
          "*"
          (Algebra.BigOperators.Basic.«term∏_,_»
           "∏"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
           ", "
           (Term.app `p [(Term.app `c.blocks_fun [`j])]))))))
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
        " in "
        (Term.paren
         "("
         [(Term.proj
           (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
           "."
           `toFinset)
          [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
         ")")
        ", "
        (Algebra.BigOperators.Basic.«term∏_,_»
         "∏"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          `r
          "*"
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" (Term.app `c.blocks_fun [`j]))
           "*"
           (Term.app `p [(Term.app `c.blocks_fun [`j])])))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_sum)] "]") []) [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k `hk] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `prod_mul_distrib)
             ","
             (Tactic.rwRule [] `prod_mul_distrib)
             ","
             (Tactic.rwRule [] `prod_pow_eq_pow_sum)
             ","
             (Tactic.rwRule [] `Composition.sum_blocks_fun)
             ","
             (Tactic.rwRule [] `prod_const)
             ","
             (Tactic.rwRule [] `card_fin)]
            "]")
           [])
          [])
         (group (Tactic.Ring.tacticRing "ring") [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `d)] []))
       " in "
       (Term.app `comp_partial_sum_target [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
       ", "
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `j)]
          [":" (Term.app `Finₓ [(Term.proj (Term.proj `d "." (fieldIdx "2")) "." `length)])]))
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         `r
         "*"
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" (Term.app (Term.proj (Term.proj `d "." (fieldIdx "2")) "." `blocksFun) [`j]))
          "*"
          (Term.app `p [(Term.app (Term.proj (Term.proj `d "." (fieldIdx "2")) "." `blocksFun) [`j])]))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `sum_sigma')] "]") []) [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.app
            `sum_le_sum_of_subset_of_nonneg
            [(Term.hole "_")
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`x `hx1 `hx2] [])]
               "=>"
               (Term.app
                `prod_nonneg
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [(Term.simpleBinder [`j `hj] [])]
                   "=>"
                   (Term.app
                    `mul_nonneg
                    [`hr
                     (Term.app
                      `mul_nonneg
                      [(Term.app `pow_nonneg [`ha (Term.hole "_")]) (Term.app `hp [(Term.hole "_")])])])))])))]))
          [])
         (group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `c)]) [])]
              "⟩"))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `hd))]
           [])
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Set.mem_to_finset)
             ","
             (Tactic.simpLemma [] [] `mem_Ico)
             ","
             (Tactic.simpLemma [] [] `mem_sigma)
             ","
             (Tactic.simpLemma [] [] `Set.mem_set_of_eq)]
            "]"]
           [(Tactic.location "at" (Tactic.locationHyp [`hd] []))])
          [])
         (group
          (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `mem_comp_partial_sum_target_iff)] "]"] [])
          [])
         (group
          (Tactic.refine'
           "refine'"
           (Term.anonymousCtor
            "⟨"
            [(Term.proj `hd "." (fieldIdx "2"))
             ","
             (Term.app `c.length_le.trans_lt [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "2"))])
             ","
             (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j] [])] "=>" (Term.hole "_")))]
            "⟩"))
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             []
             [(Term.typeSpec
               ":"
               («term_≠_»
                `c
                "≠"
                (Term.app
                 `Composition.single
                 [`k
                  (Term.app
                   `zero_lt_two.trans_le
                   [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "1"))])])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.simp
                   "simp"
                   []
                   []
                   ["["
                    [(Tactic.simpLemma [] [] `Composition.eq_single_iff_length)
                     ","
                     (Tactic.simpLemma [] [] (Term.app `ne_of_gtₓ [(Term.proj `hd "." (fieldIdx "2"))]))]
                    "]"]
                   [])
                  [])]))))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Composition.ne_single_iff)] "]")
           [(Tactic.location "at" (Tactic.locationHyp [`this] []))])
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            (Term.proj (Term.app `this [`j]) "." `trans_le)
            [(Term.app `nat.lt_succ_iff.mp [(Term.proj (Term.proj `hd "." (fieldIdx "1")) "." (fieldIdx "2"))])]))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `e)] []))
       " in "
       (Term.app `comp_partial_sum_source [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1")) `n])
       ", "
       (Algebra.BigOperators.Basic.«term∏_,_»
        "∏"
        (Lean.explicitBinders
         (Lean.unbracketedExplicitBinders
          [(Lean.binderIdent `j)]
          [":" (Term.app `Finₓ [(Term.proj `e "." (fieldIdx "1"))])]))
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         `r
         "*"
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" (Term.app (Term.proj `e "." (fieldIdx "2")) [`j]))
          "*"
          (Term.app `p [(Term.app (Term.proj `e "." (fieldIdx "2")) [`j])]))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.symm "symm") [])
         (group (Tactic.apply "apply" `comp_change_of_variables_sum) [])
         (group
          (Tactic.rintro
           "rintro"
           [(Tactic.rintroPat.one
             (Tactic.rcasesPat.tuple
              "⟨"
              [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `k)]) [])
               ","
               (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `blocks_fun)]) [])]
              "⟩"))
            (Tactic.rintroPat.one (Tactic.rcasesPat.one `H))]
           [])
          [])
         (group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`K []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.proj
                 (Term.proj
                  (Term.app
                   `comp_change_of_variables
                   [(numLit "2")
                    (Init.Logic.«term_+_» `n "+" (numLit "1"))
                    `n
                    (Term.anonymousCtor "⟨" [`k "," `blocks_fun] "⟩")
                    `H])
                  "."
                  `snd)
                 "."
                 `length)
                "="
                `k))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))))
          [])
         (group
          (Tactic.«tactic_<;>_»
           (Tactic.congr "congr" [(numLit "2")] [])
           "<;>"
           (Tactic.tacticTry_
            "try"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `K)] "]") []) [])]))))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `Finₓ.heq_fun_iff [`K.symm]))] "]")
           [])
          [])
         (group (Tactic.intro "intro" [`j]) [])
         (group
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `comp_change_of_variables_blocks_fun)] "]") [])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
       " in "
       (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_^_» `r "^" `j)
        "*"
        («term_^_»
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "1") `n])
          ", "
          (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `k) "*" (Term.app `p [`k])))
         "^"
         `j))))
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
            [(Tactic.rwRule [] `comp_partial_sum_source)
             ","
             (Tactic.rwRule
              ["←"]
              (Term.app
               `sum_sigma'
               [(Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                  "=>"
                  (Term.paren
                   "("
                   [(Term.app
                     `Fintype.piFinset
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])]
                        "=>"
                        (Term.app `Ico [(numLit "1") `n])))])
                    [(Term.typeAscription ":" (Term.app `Finset [(Term.arrow (Term.app `Finₓ [`k]) "→" (termℕ "ℕ"))]))]]
                   ")")))
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`n `e] [])]
                  "=>"
                  (Algebra.BigOperators.Basic.«term∏_,_»
                   "∏"
                   (Lean.explicitBinders
                    (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
                   ", "
                   (Finset.Data.Finset.Fold.«term_*_»
                    `r
                    "*"
                    (Finset.Data.Finset.Fold.«term_*_»
                     («term_^_» `a "^" (Term.app `e [`j]))
                     "*"
                     (Term.app `p [(Term.app `e [`j])]))))))]))]
            "]")
           [])
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma
              []
              ["←"]
              (Term.app
               (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
               [(Data.Real.Basic.termℝ "ℝ")
                (Term.app `Finₓ [`j])
                (Term.hole "_")
                (Term.hole "_")
                (Data.Real.Basic.termℝ "ℝ")]))]
            "]"]
           [])
          [])
         (group
          (Tactic.simp
           "simp"
           []
           ["only"]
           ["["
            [(Tactic.simpLemma
              []
              ["←"]
              (Term.app
               `MultilinearMap.map_sum_finset
               [(Term.app
                 `MultilinearMap.mkPiAlgebra
                 [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
                  "=>"
                  (Finset.Data.Finset.Fold.«term_*_»
                   `r
                   "*"
                   (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))]))]
            "]"]
           [])
          [])
         (group
          (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `MultilinearMap.mk_pi_algebra_apply)] "]"] [])
          [])
         (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
         (group
          (Tactic.simp
           "simp"
           []
           []
           ["["
            [(Tactic.simpLemma [] [] `prod_const)
             ","
             (Tactic.simpLemma [] ["←"] `mul_sum)
             ","
             (Tactic.simpLemma [] [] `mul_powₓ)]
            "]"]
           [])
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
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
         [(Tactic.rwRule [] `comp_partial_sum_source)
          ","
          (Tactic.rwRule
           ["←"]
           (Term.app
            `sum_sigma'
            [(Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
               "=>"
               (Term.paren
                "("
                [(Term.app
                  `Fintype.piFinset
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])]
                     "=>"
                     (Term.app `Ico [(numLit "1") `n])))])
                 [(Term.typeAscription ":" (Term.app `Finset [(Term.arrow (Term.app `Finₓ [`k]) "→" (termℕ "ℕ"))]))]]
                ")")))
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`n `e] [])]
               "=>"
               (Algebra.BigOperators.Basic.«term∏_,_»
                "∏"
                (Lean.explicitBinders
                 (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
                ", "
                (Finset.Data.Finset.Fold.«term_*_»
                 `r
                 "*"
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_^_» `a "^" (Term.app `e [`j]))
                  "*"
                  (Term.app `p [(Term.app `e [`j])]))))))]))]
         "]")
        [])
       [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `sum_congr
         [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma
           []
           ["←"]
           (Term.app
            (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
            [(Data.Real.Basic.termℝ "ℝ")
             (Term.app `Finₓ [`j])
             (Term.hole "_")
             (Term.hole "_")
             (Data.Real.Basic.termℝ "ℝ")]))]
         "]"]
        [])
       [])
      (group
       (Tactic.simp
        "simp"
        []
        ["only"]
        ["["
         [(Tactic.simpLemma
           []
           ["←"]
           (Term.app
            `MultilinearMap.map_sum_finset
            [(Term.app
              `MultilinearMap.mkPiAlgebra
              [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
               "=>"
               (Finset.Data.Finset.Fold.«term_*_»
                `r
                "*"
                (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))]))]
         "]"]
        [])
       [])
      (group
       (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `MultilinearMap.mk_pi_algebra_apply)] "]"] [])
       [])
      (group (Tactic.dsimp "dsimp" [] [] [] [] []) [])
      (group
       (Tactic.simp
        "simp"
        []
        []
        ["["
         [(Tactic.simpLemma [] [] `prod_const)
          ","
          (Tactic.simpLemma [] ["←"] `mul_sum)
          ","
          (Tactic.simpLemma [] [] `mul_powₓ)]
         "]"]
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
  (Tactic.simp
   "simp"
   []
   []
   ["["
    [(Tactic.simpLemma [] [] `prod_const)
     ","
     (Tactic.simpLemma [] ["←"] `mul_sum)
     ","
     (Tactic.simpLemma [] [] `mul_powₓ)]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_powₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_sum
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `prod_const
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.dsimp', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `MultilinearMap.mk_pi_algebra_apply)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `MultilinearMap.mk_pi_algebra_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma
      []
      ["←"]
      (Term.app
       `MultilinearMap.map_sum_finset
       [(Term.app
         `MultilinearMap.mkPiAlgebra
         [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
          "=>"
          (Finset.Data.Finset.Fold.«term_*_»
           `r
           "*"
           (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))]))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `MultilinearMap.map_sum_finset
   [(Term.app
     `MultilinearMap.mkPiAlgebra
     [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
      "=>"
      (Finset.Data.Finset.Fold.«term_*_»
       `r
       "*"
       (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))])
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
    [(Term.simpleBinder [`k] []) (Term.simpleBinder [`m] [(Term.typeSpec ":" (termℕ "ℕ"))])]
    "=>"
    (Finset.Data.Finset.Fold.«term_*_»
     `r
     "*"
     (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   `r
   "*"
   (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" `m) "*" (Term.app `p [`m]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [`m])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» `a "^" `m)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `m
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `a "^" `m) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.simpleBinder.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (termℕ "ℕ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'termℕ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `MultilinearMap.mkPiAlgebra [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Finₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finₓ [`j]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MultilinearMap.mkPiAlgebra
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   `MultilinearMap.mkPiAlgebra
   [(Data.Real.Basic.termℝ "ℝ") (Term.paren "(" [(Term.app `Finₓ [`j]) []] ")") (Data.Real.Basic.termℝ "ℝ")])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `MultilinearMap.map_sum_finset
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simp
   "simp"
   []
   ["only"]
   ["["
    [(Tactic.simpLemma
      []
      ["←"]
      (Term.app
       (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
       [(Data.Real.Basic.termℝ "ℝ")
        (Term.app `Finₓ [`j])
        (Term.hole "_")
        (Term.hole "_")
        (Data.Real.Basic.termℝ "ℝ")]))]
    "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
   [(Data.Real.Basic.termℝ "ℝ") (Term.app `Finₓ [`j]) (Term.hole "_") (Term.hole "_") (Data.Real.Basic.termℝ "ℝ")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Finₓ [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Finₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Finₓ [`j]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Data.Real.Basic.termℝ "ℝ")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Data.Real.Basic.termℝ', expected 'antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `MultilinearMap.mk_pi_algebra_apply)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.explicit', expected 'Lean.Parser.Term.explicit.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `MultilinearMap.mk_pi_algebra_apply
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'only', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app `sum_congr [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `sum_congr [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `rfl
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `sum_congr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `comp_partial_sum_source)
     ","
     (Tactic.rwRule
      ["←"]
      (Term.app
       `sum_sigma'
       [(Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
          "=>"
          (Term.paren
           "("
           [(Term.app
             `Fintype.piFinset
             [(Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])]
                "=>"
                (Term.app `Ico [(numLit "1") `n])))])
            [(Term.typeAscription ":" (Term.app `Finset [(Term.arrow (Term.app `Finₓ [`k]) "→" (termℕ "ℕ"))]))]]
           ")")))
        (Term.fun
         "fun"
         (Term.basicFun
          [(Term.simpleBinder [`n `e] [])]
          "=>"
          (Algebra.BigOperators.Basic.«term∏_,_»
           "∏"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            `r
            "*"
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» `a "^" (Term.app `e [`j]))
             "*"
             (Term.app `p [(Term.app `e [`j])]))))))]))]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwSeq', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `sum_sigma'
   [(Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k] [(Term.typeSpec ":" (termℕ "ℕ"))])]
      "=>"
      (Term.paren
       "("
       [(Term.app
         `Fintype.piFinset
         [(Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`i] [(Term.typeSpec ":" (Term.app `Finₓ [`k]))])]
            "=>"
            (Term.app `Ico [(numLit "1") `n])))])
        [(Term.typeAscription ":" (Term.app `Finset [(Term.arrow (Term.app `Finₓ [`k]) "→" (termℕ "ℕ"))]))]]
       ")")))
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`n `e] [])]
      "=>"
      (Algebra.BigOperators.Basic.«term∏_,_»
       "∏"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        `r
        "*"
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" (Term.app `e [`j]))
         "*"
         (Term.app `p [(Term.app `e [`j])]))))))])
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
    [(Term.simpleBinder [`n `e] [])]
    "=>"
    (Algebra.BigOperators.Basic.«term∏_,_»
     "∏"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      `r
      "*"
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" (Term.app `e [`j]))
       "*"
       (Term.app `p [(Term.app `e [`j])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∏_,_»
   "∏"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] [":" (Term.app `Finₓ [`n])]))
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    `r
    "*"
    (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" (Term.app `e [`j])) "*" (Term.app `p [(Term.app `e [`j])]))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∏_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   `r
   "*"
   (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" (Term.app `e [`j])) "*" (Term.app `p [(Term.app `e [`j])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» («term_^_» `a "^" (Term.app `e [`j])) "*" (Term.app `p [(Term.app `e [`j])]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p [(Term.app `e [`j])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `e [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `e [`j]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» `a "^" (Term.app `e [`j]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `e [`j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `e
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `a "^" (Term.app `e [`j])) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `r
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.explicitBinders', expected 'Mathlib.ExtendedBinder.extBinders'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
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
    First technical lemma to control the growth of coefficients of the inverse. Bound the explicit
    expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
    in a general abstract setup. -/
  theorem
    radius_right_inv_pos_of_radius_pos_aux1
    ( n : ℕ ) ( p : ℕ → ℝ ) ( hp : ∀ k , 0 ≤ p k ) { r a : ℝ } ( hr : 0 ≤ r ) ( ha : 0 ≤ a )
      :
        ∑
            k
            in
            Ico 2 n + 1
            ,
            a ^ k
              *
              ∑
                c
                in
                ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                ,
                r ^ c.length * ∏ j , p c.blocks_fun j
          ≤
          ∑ j in Ico 2 n + 1 , r ^ j * ∑ k in Ico 1 n , a ^ k * p k ^ j
    :=
      calc
        ∑
                k
                in
                Ico 2 n + 1
                ,
                a ^ k
                  *
                  ∑
                    c
                    in
                    ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                    ,
                    r ^ c.length * ∏ j , p c.blocks_fun j
              =
              ∑
                k
                in
                Ico 2 n + 1
                ,
                ∑
                  c
                  in
                  ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                  ,
                  ∏ j , r * a ^ c.blocks_fun j * p c.blocks_fun j
            :=
            by
              simp_rw [ mul_sum ]
                apply sum_congr rfl fun k hk => _
                apply sum_congr rfl fun c hc => _
                rw
                  [
                    prod_mul_distrib
                      ,
                      prod_mul_distrib
                      ,
                      prod_pow_eq_pow_sum
                      ,
                      Composition.sum_blocks_fun
                      ,
                      prod_const
                      ,
                      card_fin
                    ]
                ring
          _
              ≤
              ∑
                d
                in
                comp_partial_sum_target 2 n + 1 n
                ,
                ∏ j : Finₓ d . 2 . length , r * a ^ d . 2 . blocksFun j * p d . 2 . blocksFun j
            :=
            by
              rw [ sum_sigma' ]
                refine'
                  sum_le_sum_of_subset_of_nonneg
                    _ fun x hx1 hx2 => prod_nonneg fun j hj => mul_nonneg hr mul_nonneg pow_nonneg ha _ hp _
                rintro ⟨ k , c ⟩ hd
                simp only [ Set.mem_to_finset , mem_Ico , mem_sigma , Set.mem_set_of_eq ] at hd
                simp only [ mem_comp_partial_sum_target_iff ]
                refine' ⟨ hd . 2 , c.length_le.trans_lt hd . 1 . 2 , fun j => _ ⟩
                have
                  : c ≠ Composition.single k zero_lt_two.trans_le hd . 1 . 1
                    :=
                    by simp [ Composition.eq_single_iff_length , ne_of_gtₓ hd . 2 ]
                rw [ Composition.ne_single_iff ] at this
                exact this j . trans_le nat.lt_succ_iff.mp hd . 1 . 2
          _ = ∑ e in comp_partial_sum_source 2 n + 1 n , ∏ j : Finₓ e . 1 , r * a ^ e . 2 j * p e . 2 j
            :=
            by
              symm
                apply comp_change_of_variables_sum
                rintro ⟨ k , blocks_fun ⟩ H
                have K : comp_change_of_variables 2 n + 1 n ⟨ k , blocks_fun ⟩ H . snd . length = k := by simp
                congr 2 <;> try rw [ K ]
                rw [ Finₓ.heq_fun_iff K.symm ]
                intro j
                rw [ comp_change_of_variables_blocks_fun ]
          _ = ∑ j in Ico 2 n + 1 , r ^ j * ∑ k in Ico 1 n , a ^ k * p k ^ j
            :=
            by
              rw
                  [
                    comp_partial_sum_source
                      ,
                      ←
                        sum_sigma'
                          Ico 2 n + 1
                            fun k : ℕ => ( Fintype.piFinset fun i : Finₓ k => Ico 1 n : Finset Finₓ k → ℕ )
                            fun n e => ∏ j : Finₓ n , r * a ^ e j * p e j
                    ]
                apply sum_congr rfl fun j hj => _
                simp only [ ← @ MultilinearMap.mk_pi_algebra_apply ℝ Finₓ j _ _ ℝ ]
                simp
                  only
                  [
                    ← MultilinearMap.map_sum_finset MultilinearMap.mkPiAlgebra ℝ Finₓ j ℝ fun k m : ℕ => r * a ^ m * p m
                    ]
                simp only [ MultilinearMap.mk_pi_algebra_apply ]
                dsimp
                simp [ prod_const , ← mul_sum , mul_powₓ ]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit\nexpression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,\nin the specific setup we are interesting in, by reducing to the general bound in\n`radius_right_inv_pos_of_radius_pos_aux1`. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `radius_right_inv_pos_of_radius_pos_aux2 [])
  (Command.declSig
   [(Term.implicitBinder "{" [`n] [":" (termℕ "ℕ")] "}")
    (Term.explicitBinder "(" [`hn] [":" («term_≤_» (numLit "2") "≤" (Init.Logic.«term_+_» `n "+" (numLit "1")))] [] ")")
    (Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")
    (Term.implicitBinder "{" [`r `a `C] [":" (Data.Real.Basic.termℝ "ℝ")] "}")
    (Term.explicitBinder "(" [`hr] [":" («term_≤_» (numLit "0") "≤" `r)] [] ")")
    (Term.explicitBinder "(" [`ha] [":" («term_≤_» (numLit "0") "≤" `a)] [] ")")
    (Term.explicitBinder "(" [`hC] [":" («term_≤_» (numLit "0") "≤" `C)] [] ")")
    (Term.explicitBinder
     "("
     [`hp]
     [":"
      (Term.forall
       "∀"
       [(Term.simpleBinder [`n] [])]
       ","
       («term_≤_»
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
        "≤"
        (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `n))))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_≤_»
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
      " in "
      (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" `k)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
     "≤"
     (Init.Logic.«term_+_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥»
        "∥"
        (Term.paren
         "("
         [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
         ")")
        "∥")
       "*"
       `a)
      "+"
      (Finset.Data.Finset.Fold.«term_*_»
       (Finset.Data.Finset.Fold.«term_*_»
        (Analysis.Normed.Group.Basic.«term∥_∥»
         "∥"
         (Term.paren
          "("
          [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
          ")")
         "∥")
        "*"
        `C)
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        («term_^_»
         (Finset.Data.Finset.Fold.«term_*_»
          `r
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
           " in "
           (Term.app `Ico [(numLit "1") `n])
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `a "^" `j)
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
         "^"
         `k)))))))
  (Command.declValSimple
   ":="
   (Term.let
    "let"
    (Term.letDecl
     (Term.letIdDecl
      `I
      []
      []
      ":="
      (Analysis.Normed.Group.Basic.«term∥_∥»
       "∥"
       (Term.paren
        "("
        [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
        ")")
       "∥")))
    []
    (calc
     "calc"
     [(calcStep
       («term_=_»
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `k)
          "*"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
        "="
        (Init.Logic.«term_+_»
         (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
         "+"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" `k)
           "*"
           (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))
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
             ["["
              [(Tactic.simpLemma [] [] `LinearIsometryEquiv.norm_map)
               ","
               (Tactic.simpLemma [] [] `pow_oneₓ)
               ","
               (Tactic.simpLemma [] [] `right_inv_coeff_one)
               ","
               (Tactic.simpLemma [] [] `Nat.Ico_succ_singleton)
               ","
               (Tactic.simpLemma [] [] `sum_singleton)
               ","
               (Tactic.simpLemma [] ["←"] (Term.app `sum_Ico_consecutive [(Term.hole "_") `one_le_two `hn]))]
              "]"]
             [])
            [])]))))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Init.Logic.«term_+_»
         (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
         "+"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" `k)
           "*"
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Term.app
             (Term.proj
              (Term.paren
               "("
               [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
               ")")
              "."
              `compContinuousMultilinearMap)
             [(Algebra.BigOperators.Basic.«term∑_in_,_»
               "∑"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
               " in "
               (Term.paren
                "("
                [(Term.proj
                  (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                  "."
                  `toFinset)
                 [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
                ")")
               ", "
               (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])
            "∥")))))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group (Tactic.congr "congr" [(numLit "1")] []) [])
           (group
            (Tactic.apply
             "apply"
             (Term.app
              `sum_congr
              [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule
                []
                (Term.app
                 `right_inv_coeff
                 [(Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.proj (Term.app (Term.proj `mem_Ico "." (fieldIdx "1")) [`hj]) "." (fieldIdx "1"))]))
               ","
               (Tactic.rwRule [] `norm_neg)]
              "]")
             [])
            [])]))))
      (calcStep
       («term_≤_»
        (Term.hole "_")
        "≤"
        (Init.Logic.«term_+_»
         (Finset.Data.Finset.Fold.«term_*_»
          `a
          "*"
          (Analysis.Normed.Group.Basic.«term∥_∥»
           "∥"
           (Term.paren
            "("
            [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
            ")")
           "∥"))
         "+"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" `k)
           "*"
           (Finset.Data.Finset.Fold.«term_*_»
            `I
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
             " in "
             (Term.paren
              "("
              [(Term.proj
                (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                "."
                `toFinset)
               [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
              ")")
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `c.length))
              "*"
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               (Analysis.Normed.Group.Basic.«term∥_∥»
                "∥"
                (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
                "∥")))))))))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.applyRules
             "apply_rules"
             []
             "["
             [`add_le_add
              ","
              `le_reflₓ
              ","
              (Term.app
               `sum_le_sum
               [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))])
              ","
              `mul_le_mul_of_nonneg_left
              ","
              `pow_nonneg
              ","
              `ha]
             "]"
             [])
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.proj
              (Term.app `ContinuousLinearMap.norm_comp_continuous_multilinear_map_le [(Term.hole "_") (Term.hole "_")])
              "."
              `trans))
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") (Term.app `norm_nonneg [(Term.hole "_")])]))
            [])
           (group
            (Tactic.apply "apply" (Term.proj (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans))
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.app
              `sum_le_sum
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))]))
            [])
           (group
            (Tactic.apply
             "apply"
             (Term.proj
              (Term.app `comp_along_composition_norm [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
              "."
              `trans))
            [])
           (group (Tactic.apply "apply" (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hp [(Term.hole "_")])])) [])
           (group
            (Tactic.exact
             "exact"
             (Term.app
              `prod_nonneg
              [(Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))]))
            [])]))))
      (calcStep
       («term_=_»
        (Term.hole "_")
        "="
        (Init.Logic.«term_+_»
         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
         "+"
         (Finset.Data.Finset.Fold.«term_*_»
          (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
           " in "
           (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `a "^" `k)
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
             " in "
             (Term.paren
              "("
              [(Term.proj
                (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                "."
                `toFinset)
               [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
              ")")
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              («term_^_» `r "^" `c.length)
              "*"
              (Algebra.BigOperators.Basic.«term∏_,_»
               "∏"
               (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
               ", "
               (Analysis.Normed.Group.Basic.«term∥_∥»
                "∥"
                (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
                "∥")))))))))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.simpRw
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] (Term.app `mul_assocₓ [`C]))
               ","
               (Tactic.rwRule ["←"] `mul_sum)
               ","
               (Tactic.rwRule ["←"] `mul_assocₓ)
               ","
               (Tactic.rwRule
                []
                (Term.app
                 `mul_commₓ
                 [(Term.hole "_") (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Init.Coe.«term↑_» "↑" `i.symm) "∥")]))
               ","
               (Tactic.rwRule [] `mul_assocₓ)
               ","
               (Tactic.rwRule ["←"] `mul_sum)
               ","
               (Tactic.rwRule ["←"] `mul_assocₓ)
               ","
               (Tactic.rwRule [] (Term.app `mul_commₓ [(Term.hole "_") `C]))
               ","
               (Tactic.rwRule [] `mul_assocₓ)
               ","
               (Tactic.rwRule ["←"] `mul_sum)]
              "]")
             [])
            [])
           (group (Tactic.Ring.tacticRing "ring") [])]))))
      (calcStep
       («term_≤_»
        (Term.hole "_")
        "≤"
        (Init.Logic.«term_+_»
         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
         "+"
         (Finset.Data.Finset.Fold.«term_*_»
          (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
           " in "
           (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
           ", "
           («term_^_»
            (Finset.Data.Finset.Fold.«term_*_»
             `r
             "*"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              " in "
              (Term.app `Ico [(numLit "1") `n])
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               («term_^_» `a "^" `j)
               "*"
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
            "^"
            `k)))))
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.applyRules
             "apply_rules"
             []
             "["
             [`add_le_add "," `le_reflₓ "," `mul_le_mul_of_nonneg_left "," `norm_nonneg "," `hC "," `mul_nonneg]
             "]"
             [])
            [])
           (group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ)] "]") []) [])
           (group
            (Tactic.apply
             "apply"
             (Term.app
              `radius_right_inv_pos_of_radius_pos_aux1
              [`n
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`k] [])]
                 "=>"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
               (Term.fun
                "fun"
                (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
               `hr
               `ha]))
            [])]))))]))
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
  (Term.let
   "let"
   (Term.letDecl
    (Term.letIdDecl
     `I
     []
     []
     ":="
     (Analysis.Normed.Group.Basic.«term∥_∥»
      "∥"
      (Term.paren
       "("
       [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
       ")")
      "∥")))
   []
   (calc
    "calc"
    [(calcStep
      («term_=_»
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `k)
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
       "="
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
        "+"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `k)
          "*"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))
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
            ["["
             [(Tactic.simpLemma [] [] `LinearIsometryEquiv.norm_map)
              ","
              (Tactic.simpLemma [] [] `pow_oneₓ)
              ","
              (Tactic.simpLemma [] [] `right_inv_coeff_one)
              ","
              (Tactic.simpLemma [] [] `Nat.Ico_succ_singleton)
              ","
              (Tactic.simpLemma [] [] `sum_singleton)
              ","
              (Tactic.simpLemma [] ["←"] (Term.app `sum_Ico_consecutive [(Term.hole "_") `one_le_two `hn]))]
             "]"]
            [])
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
        "+"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `k)
          "*"
          (Analysis.Normed.Group.Basic.«term∥_∥»
           "∥"
           (Term.app
            (Term.proj
             (Term.paren
              "("
              [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
              ")")
             "."
             `compContinuousMultilinearMap)
            [(Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
              " in "
              (Term.paren
               "("
               [(Term.proj
                 (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                 "."
                 `toFinset)
                [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
               ")")
              ", "
              (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])
           "∥")))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group (Tactic.congr "congr" [(numLit "1")] []) [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `sum_congr
             [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule
               []
               (Term.app
                `right_inv_coeff
                [(Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.proj (Term.app (Term.proj `mem_Ico "." (fieldIdx "1")) [`hj]) "." (fieldIdx "1"))]))
              ","
              (Tactic.rwRule [] `norm_neg)]
             "]")
            [])
           [])]))))
     (calcStep
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_»
         `a
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥»
          "∥"
          (Term.paren
           "("
           [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
           ")")
          "∥"))
        "+"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `k)
          "*"
          (Finset.Data.Finset.Fold.«term_*_»
           `I
           "*"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
            " in "
            (Term.paren
             "("
             [(Term.proj
               (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
               "."
               `toFinset)
              [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
             ")")
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `c.length))
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
               "∥")))))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.applyRules
            "apply_rules"
            []
            "["
            [`add_le_add
             ","
             `le_reflₓ
             ","
             (Term.app
              `sum_le_sum
              [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))])
             ","
             `mul_le_mul_of_nonneg_left
             ","
             `pow_nonneg
             ","
             `ha]
            "]"
            [])
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.app `ContinuousLinearMap.norm_comp_continuous_multilinear_map_le [(Term.hole "_") (Term.hole "_")])
             "."
             `trans))
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") (Term.app `norm_nonneg [(Term.hole "_")])]))
           [])
          (group
           (Tactic.apply "apply" (Term.proj (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans))
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `sum_le_sum
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))]))
           [])
          (group
           (Tactic.apply
            "apply"
            (Term.proj
             (Term.app `comp_along_composition_norm [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
             "."
             `trans))
           [])
          (group (Tactic.apply "apply" (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hp [(Term.hole "_")])])) [])
          (group
           (Tactic.exact
            "exact"
            (Term.app
             `prod_nonneg
             [(Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))]))
           [])]))))
     (calcStep
      («term_=_»
       (Term.hole "_")
       "="
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
        "+"
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
         "*"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          (Finset.Data.Finset.Fold.«term_*_»
           («term_^_» `a "^" `k)
           "*"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
            " in "
            (Term.paren
             "("
             [(Term.proj
               (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
               "."
               `toFinset)
              [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
             ")")
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» `r "^" `c.length)
             "*"
             (Algebra.BigOperators.Basic.«term∏_,_»
              "∏"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
              ", "
              (Analysis.Normed.Group.Basic.«term∥_∥»
               "∥"
               (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
               "∥")))))))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.simpRw
            "simp_rw"
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] (Term.app `mul_assocₓ [`C]))
              ","
              (Tactic.rwRule ["←"] `mul_sum)
              ","
              (Tactic.rwRule ["←"] `mul_assocₓ)
              ","
              (Tactic.rwRule
               []
               (Term.app
                `mul_commₓ
                [(Term.hole "_") (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Init.Coe.«term↑_» "↑" `i.symm) "∥")]))
              ","
              (Tactic.rwRule [] `mul_assocₓ)
              ","
              (Tactic.rwRule ["←"] `mul_sum)
              ","
              (Tactic.rwRule ["←"] `mul_assocₓ)
              ","
              (Tactic.rwRule [] (Term.app `mul_commₓ [(Term.hole "_") `C]))
              ","
              (Tactic.rwRule [] `mul_assocₓ)
              ","
              (Tactic.rwRule ["←"] `mul_sum)]
             "]")
            [])
           [])
          (group (Tactic.Ring.tacticRing "ring") [])]))))
     (calcStep
      («term_≤_»
       (Term.hole "_")
       "≤"
       (Init.Logic.«term_+_»
        (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
        "+"
        (Finset.Data.Finset.Fold.«term_*_»
         (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
         "*"
         (Algebra.BigOperators.Basic.«term∑_in_,_»
          "∑"
          (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
          " in "
          (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
          ", "
          («term_^_»
           (Finset.Data.Finset.Fold.«term_*_»
            `r
            "*"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             " in "
             (Term.app `Ico [(numLit "1") `n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              («term_^_» `a "^" `j)
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
           "^"
           `k)))))
      ":="
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(group
           (Tactic.applyRules
            "apply_rules"
            []
            "["
            [`add_le_add "," `le_reflₓ "," `mul_le_mul_of_nonneg_left "," `norm_nonneg "," `hC "," `mul_nonneg]
            "]"
            [])
           [])
          (group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ)] "]") []) [])
          (group
           (Tactic.apply
            "apply"
            (Term.app
             `radius_right_inv_pos_of_radius_pos_aux1
             [`n
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`k] [])]
                "=>"
                (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
              (Term.fun
               "fun"
               (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
              `hr
              `ha]))
           [])]))))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.let', expected 'Lean.Parser.Term.let.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (calc
   "calc"
   [(calcStep
     («term_=_»
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_^_» `a "^" `k)
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
      "="
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
       "+"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `k)
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))
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
           ["["
            [(Tactic.simpLemma [] [] `LinearIsometryEquiv.norm_map)
             ","
             (Tactic.simpLemma [] [] `pow_oneₓ)
             ","
             (Tactic.simpLemma [] [] `right_inv_coeff_one)
             ","
             (Tactic.simpLemma [] [] `Nat.Ico_succ_singleton)
             ","
             (Tactic.simpLemma [] [] `sum_singleton)
             ","
             (Tactic.simpLemma [] ["←"] (Term.app `sum_Ico_consecutive [(Term.hole "_") `one_le_two `hn]))]
            "]"]
           [])
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» `a "*" `I)
       "+"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `k)
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥»
          "∥"
          (Term.app
           (Term.proj
            (Term.paren
             "("
             [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
             ")")
            "."
            `compContinuousMultilinearMap)
           [(Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
             " in "
             (Term.paren
              "("
              [(Term.proj
                (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
                "."
                `toFinset)
               [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
              ")")
             ", "
             (Term.app `p.comp_along_composition [(Term.app `p.right_inv [`i]) `c]))])
          "∥")))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.congr "congr" [(numLit "1")] []) [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `sum_congr
            [`rfl (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule
              []
              (Term.app
               `right_inv_coeff
               [(Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.proj (Term.app (Term.proj `mem_Ico "." (fieldIdx "1")) [`hj]) "." (fieldIdx "1"))]))
             ","
             (Tactic.rwRule [] `norm_neg)]
            "]")
           [])
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_»
        `a
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥»
         "∥"
         (Term.paren
          "("
          [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
          ")")
         "∥"))
       "+"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
        " in "
        (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `k)
         "*"
         (Finset.Data.Finset.Fold.«term_*_»
          `I
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
           " in "
           (Term.paren
            "("
            [(Term.proj
              (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
              "."
              `toFinset)
             [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
            ")")
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `c.length))
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥»
              "∥"
              (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
              "∥")))))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.applyRules
           "apply_rules"
           []
           "["
           [`add_le_add
            ","
            `le_reflₓ
            ","
            (Term.app
             `sum_le_sum
             [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.hole "_")))])
            ","
            `mul_le_mul_of_nonneg_left
            ","
            `pow_nonneg
            ","
            `ha]
           "]"
           [])
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.app `ContinuousLinearMap.norm_comp_continuous_multilinear_map_le [(Term.hole "_") (Term.hole "_")])
            "."
            `trans))
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.app `mul_le_mul_of_nonneg_left [(Term.hole "_") (Term.app `norm_nonneg [(Term.hole "_")])]))
          [])
         (group
          (Tactic.apply "apply" (Term.proj (Term.app `norm_sum_le [(Term.hole "_") (Term.hole "_")]) "." `trans))
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `sum_le_sum
            [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`c `hc] [])] "=>" (Term.hole "_")))]))
          [])
         (group
          (Tactic.apply
           "apply"
           (Term.proj
            (Term.app `comp_along_composition_norm [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            "."
            `trans))
          [])
         (group (Tactic.apply "apply" (Term.app `mul_le_mul_of_nonneg_right [(Term.app `hp [(Term.hole "_")])])) [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `prod_nonneg
            [(Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`j `hj] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))]))
          [])]))))
    (calcStep
     («term_=_»
      (Term.hole "_")
      "="
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
       "+"
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
        "*"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `k)
          "*"
          (Algebra.BigOperators.Basic.«term∑_in_,_»
           "∑"
           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `c)] []))
           " in "
           (Term.paren
            "("
            [(Term.proj
              (Set.«term{_|_}» "{" `c "|" («term_<_» (numLit "1") "<" (Term.app `Composition.length [`c])) "}")
              "."
              `toFinset)
             [(Term.typeAscription ":" (Term.app `Finset [(Term.app `Composition [`k])]))]]
            ")")
           ", "
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `r "^" `c.length)
            "*"
            (Algebra.BigOperators.Basic.«term∏_,_»
             "∏"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
             ", "
             (Analysis.Normed.Group.Basic.«term∥_∥»
              "∥"
              (Term.app `p.right_inv [`i (Term.app `c.blocks_fun [`j])])
              "∥")))))))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.simpRw
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] (Term.app `mul_assocₓ [`C]))
             ","
             (Tactic.rwRule ["←"] `mul_sum)
             ","
             (Tactic.rwRule ["←"] `mul_assocₓ)
             ","
             (Tactic.rwRule
              []
              (Term.app
               `mul_commₓ
               [(Term.hole "_") (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Init.Coe.«term↑_» "↑" `i.symm) "∥")]))
             ","
             (Tactic.rwRule [] `mul_assocₓ)
             ","
             (Tactic.rwRule ["←"] `mul_sum)
             ","
             (Tactic.rwRule ["←"] `mul_assocₓ)
             ","
             (Tactic.rwRule [] (Term.app `mul_commₓ [(Term.hole "_") `C]))
             ","
             (Tactic.rwRule [] `mul_assocₓ)
             ","
             (Tactic.rwRule ["←"] `mul_sum)]
            "]")
           [])
          [])
         (group (Tactic.Ring.tacticRing "ring") [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Init.Logic.«term_+_»
       (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
       "+"
       (Finset.Data.Finset.Fold.«term_*_»
        (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
        "*"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
         " in "
         (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
         ", "
         («term_^_»
          (Finset.Data.Finset.Fold.«term_*_»
           `r
           "*"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
            " in "
            (Term.app `Ico [(numLit "1") `n])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» `a "^" `j)
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
          "^"
          `k)))))
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (Tactic.applyRules
           "apply_rules"
           []
           "["
           [`add_le_add "," `le_reflₓ "," `mul_le_mul_of_nonneg_left "," `norm_nonneg "," `hC "," `mul_nonneg]
           "]"
           [])
          [])
         (group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ)] "]") []) [])
         (group
          (Tactic.apply
           "apply"
           (Term.app
            `radius_right_inv_pos_of_radius_pos_aux1
            [`n
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k] [])]
               "=>"
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
             (Term.fun
              "fun"
              (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
             `hr
             `ha]))
          [])]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calc', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.applyRules
        "apply_rules"
        []
        "["
        [`add_le_add "," `le_reflₓ "," `mul_le_mul_of_nonneg_left "," `norm_nonneg "," `hC "," `mul_nonneg]
        "]"
        [])
       [])
      (group (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ)] "]") []) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `radius_right_inv_pos_of_radius_pos_aux1
         [`n
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`k] [])]
            "=>"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
          `hr
          `ha]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.apply
   "apply"
   (Term.app
    `radius_right_inv_pos_of_radius_pos_aux1
    [`n
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`k] [])]
       "=>"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
     (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
     `hr
     `ha]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.apply', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `radius_right_inv_pos_of_radius_pos_aux1
   [`n
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [`k] [])]
      "=>"
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
    (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
    `hr
    `ha])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ha
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `hr
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`k] [])] "=>" (Term.app `norm_nonneg [(Term.hole "_")]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`k] [])]
    "=>"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.right_inv [`i `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`k] [])]
    "=>"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
  []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `radius_right_inv_pos_of_radius_pos_aux1
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.simpRw "simp_rw" (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mul_powₓ)] "]") [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpRw', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_powₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.applyRules
   "apply_rules"
   []
   "["
   [`add_le_add "," `le_reflₓ "," `mul_le_mul_of_nonneg_left "," `norm_nonneg "," `hC "," `mul_nonneg]
   "]"
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.applyRules', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hC
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `norm_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_le_mul_of_nonneg_left
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `le_reflₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `add_le_add
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Init.Logic.«term_+_»
    (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
    "+"
    (Finset.Data.Finset.Fold.«term_*_»
     (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
     "*"
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
      " in "
      (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
      ", "
      («term_^_»
       (Finset.Data.Finset.Fold.«term_*_»
        `r
        "*"
        (Algebra.BigOperators.Basic.«term∑_in_,_»
         "∑"
         (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
         " in "
         (Term.app `Ico [(numLit "1") `n])
         ", "
         (Finset.Data.Finset.Fold.«term_*_»
          («term_^_» `a "^" `j)
          "*"
          (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
       "^"
       `k)))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_»
   (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
   "+"
   (Finset.Data.Finset.Fold.«term_*_»
    (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
    "*"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
     " in "
     (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
     ", "
     («term_^_»
      (Finset.Data.Finset.Fold.«term_*_»
       `r
       "*"
       (Algebra.BigOperators.Basic.«term∑_in_,_»
        "∑"
        (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
        " in "
        (Term.app `Ico [(numLit "1") `n])
        ", "
        (Finset.Data.Finset.Fold.«term_*_»
         («term_^_» `a "^" `j)
         "*"
         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
      "^"
      `k))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
   "*"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    ", "
    («term_^_»
     (Finset.Data.Finset.Fold.«term_*_»
      `r
      "*"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
       " in "
       (Term.app `Ico [(numLit "1") `n])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_^_» `a "^" `j)
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
     "^"
     `k)))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   ", "
   («term_^_»
    (Finset.Data.Finset.Fold.«term_*_»
     `r
     "*"
     (Algebra.BigOperators.Basic.«term∑_in_,_»
      "∑"
      (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
      " in "
      (Term.app `Ico [(numLit "1") `n])
      ", "
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" `j)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
    "^"
    `k))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_^_»
   (Finset.Data.Finset.Fold.«term_*_»
    `r
    "*"
    (Algebra.BigOperators.Basic.«term∑_in_,_»
     "∑"
     (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
     " in "
     (Term.app `Ico [(numLit "1") `n])
     ", "
     (Finset.Data.Finset.Fold.«term_*_»
      («term_^_» `a "^" `j)
      "*"
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
   "^"
   `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  (Finset.Data.Finset.Fold.«term_*_»
   `r
   "*"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
    " in "
    (Term.app `Ico [(numLit "1") `n])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     («term_^_» `a "^" `j)
     "*"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `j)] []))
   " in "
   (Term.app `Ico [(numLit "1") `n])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    («term_^_» `a "^" `j)
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_^_» `a "^" `j)
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `j]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.right_inv [`i `j])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» `a "^" `j)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `j
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `a "^" `j) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ico [(numLit "1") `n])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ico
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
    Second technical lemma to control the growth of coefficients of the inverse. Bound the explicit
    expression for `∑_{k<n+1} aᵏ Qₖ` in terms of a sum of powers of the same sum one step before,
    in the specific setup we are interesting in, by reducing to the general bound in
    `radius_right_inv_pos_of_radius_pos_aux1`. -/
  theorem
    radius_right_inv_pos_of_radius_pos_aux2
    { n : ℕ }
        ( hn : 2 ≤ n + 1 )
        ( p : FormalMultilinearSeries 𝕜 E F )
        ( i : E ≃L[ 𝕜 ] F )
        { r a C : ℝ }
        ( hr : 0 ≤ r )
        ( ha : 0 ≤ a )
        ( hC : 0 ≤ C )
        ( hp : ∀ n , ∥ p n ∥ ≤ C * r ^ n )
      :
        ∑ k in Ico 1 n + 1 , a ^ k * ∥ p.right_inv i k ∥
          ≤
          ∥ ( i.symm : F →L[ 𝕜 ] E ) ∥ * a
            +
            ∥ ( i.symm : F →L[ 𝕜 ] E ) ∥ * C * ∑ k in Ico 2 n + 1 , r * ∑ j in Ico 1 n , a ^ j * ∥ p.right_inv i j ∥ ^ k
    :=
      let
        I := ∥ ( i.symm : F →L[ 𝕜 ] E ) ∥
        calc
          ∑ k in Ico 1 n + 1 , a ^ k * ∥ p.right_inv i k ∥ = a * I + ∑ k in Ico 2 n + 1 , a ^ k * ∥ p.right_inv i k ∥
              :=
              by
                simp
                  only
                  [
                    LinearIsometryEquiv.norm_map
                      ,
                      pow_oneₓ
                      ,
                      right_inv_coeff_one
                      ,
                      Nat.Ico_succ_singleton
                      ,
                      sum_singleton
                      ,
                      ← sum_Ico_consecutive _ one_le_two hn
                    ]
            _
                =
                a * I
                  +
                  ∑
                    k
                    in
                    Ico 2 n + 1
                    ,
                    a ^ k
                      *
                      ∥
                        ( i.symm : F →L[ 𝕜 ] E ) . compContinuousMultilinearMap
                          ∑
                            c
                            in
                            ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                            ,
                            p.comp_along_composition p.right_inv i c
                        ∥
              :=
              by congr 1 apply sum_congr rfl fun j hj => _ rw [ right_inv_coeff _ _ _ mem_Ico . 1 hj . 1 , norm_neg ]
            _
                ≤
                a * ∥ ( i.symm : F →L[ 𝕜 ] E ) ∥
                  +
                  ∑
                    k
                    in
                    Ico 2 n + 1
                    ,
                    a ^ k
                      *
                      I
                        *
                        ∑
                          c
                          in
                          ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                          ,
                          C * r ^ c.length * ∏ j , ∥ p.right_inv i c.blocks_fun j ∥
              :=
              by
                apply_rules
                    [
                    add_le_add , le_reflₓ , sum_le_sum fun j hj => _ , mul_le_mul_of_nonneg_left , pow_nonneg , ha
                    ]
                  apply ContinuousLinearMap.norm_comp_continuous_multilinear_map_le _ _ . trans
                  apply mul_le_mul_of_nonneg_left _ norm_nonneg _
                  apply norm_sum_le _ _ . trans
                  apply sum_le_sum fun c hc => _
                  apply comp_along_composition_norm _ _ _ . trans
                  apply mul_le_mul_of_nonneg_right hp _
                  exact prod_nonneg fun j hj => norm_nonneg _
            _
                =
                I * a
                  +
                  I * C
                    *
                    ∑
                      k
                      in
                      Ico 2 n + 1
                      ,
                      a ^ k
                        *
                        ∑
                          c
                          in
                          ( { c | 1 < Composition.length c } . toFinset : Finset Composition k )
                          ,
                          r ^ c.length * ∏ j , ∥ p.right_inv i c.blocks_fun j ∥
              :=
              by
                simp_rw
                    [
                      mul_assocₓ C
                        ,
                        ← mul_sum
                        ,
                        ← mul_assocₓ
                        ,
                        mul_commₓ _ ∥ ↑ i.symm ∥
                        ,
                        mul_assocₓ
                        ,
                        ← mul_sum
                        ,
                        ← mul_assocₓ
                        ,
                        mul_commₓ _ C
                        ,
                        mul_assocₓ
                        ,
                        ← mul_sum
                      ]
                  ring
            _ ≤ I * a + I * C * ∑ k in Ico 2 n + 1 , r * ∑ j in Ico 1 n , a ^ j * ∥ p.right_inv i j ∥ ^ k
              :=
              by
                apply_rules [ add_le_add , le_reflₓ , mul_le_mul_of_nonneg_left , norm_nonneg , hC , mul_nonneg ]
                  simp_rw [ mul_powₓ ]
                  apply
                    radius_right_inv_pos_of_radius_pos_aux1 n fun k => ∥ p.right_inv i k ∥ fun k => norm_nonneg _ hr ha

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    " If a a formal multilinear series has a positive radius of convergence, then its right inverse\nalso has a positive radius of convergence. -/")]
  []
  []
  []
  []
  [])
 (Command.theorem
  "theorem"
  (Command.declId `radius_right_inv_pos_of_radius_pos [])
  (Command.declSig
   [(Term.explicitBinder "(" [`p] [":" (Term.app `FormalMultilinearSeries [`𝕜 `E `F])] [] ")")
    (Term.explicitBinder "(" [`i] [":" (Topology.Algebra.Module.«term_≃L[_]_» `E " ≃L[" `𝕜 "] " `F)] [] ")")
    (Term.explicitBinder "(" [`hp] [":" («term_<_» (numLit "0") "<" `p.radius)] [] ")")]
   (Term.typeSpec ":" («term_<_» (numLit "0") "<" (Term.proj (Term.app `p.right_inv [`i]) "." `radius))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Cpos)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rpos)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ple)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `C) (Lean.binderIdent `r)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hC)] ":" («term_<_» (numLit "0") "<" `C) ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hr)] ":" («term_<_» (numLit "0") "<" `r) ")")])
           ","
           (Term.forall
            "∀"
            [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
            ","
            («term_≤_»
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
             "≤"
             (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `n)))))]
         [":=" [(Term.app `le_mul_pow_of_radius_pos [`p `hp])]])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `I
           []
           ":="
           (Analysis.Normed.Group.Basic.«term∥_∥»
            "∥"
            (Term.paren
             "("
             [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
             ")")
            "∥"))))
        [])
       (group
        (Tactic.obtain
         "obtain"
         [(Tactic.rcasesPatMed
           [(Tactic.rcasesPat.tuple
             "⟨"
             [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `apos)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha1)]) [])
              ","
              (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha2)]) [])]
             "⟩")])]
         [":"
          («term∃_,_»
           "∃"
           (Lean.explicitBinders
            [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
             (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `apos)] ":" («term_<_» (numLit "0") "<" `a) ")")])
           ","
           («term_∧_»
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_»
                (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I) "*" `C)
                "*"
                («term_^_» `r "^" (numLit "2")))
               "*"
               («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
              "*"
              `a)
             "≤"
             (numLit "1"))
            "∧"
            («term_≤_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
              "*"
              `a)
             "≤"
             («term_/_» (numLit "1") "/" (numLit "2")))))]
         [])
        [])
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
                []
                [(Term.typeSpec
                  ":"
                  (Term.app
                   `tendsto
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`a] [])]
                      "=>"
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_»
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                          "*"
                          `C)
                         "*"
                         («term_^_» `r "^" (numLit "2")))
                        "*"
                        («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                       "*"
                       `a)))
                    (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                    (Term.app
                     (Topology.Basic.term𝓝 "𝓝")
                     [(Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_»
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                          "*"
                          `C)
                         "*"
                         («term_^_» `r "^" (numLit "2")))
                        "*"
                        («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                       "*"
                       (numLit "0"))])]))]
                ":="
                (Term.app `tendsto_const_nhds.mul [`tendsto_id]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`A []]
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                   " in "
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                   ", "
                   («term_<_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_»
                        (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                        "*"
                        `C)
                       "*"
                       («term_^_» `r "^" (numLit "2")))
                      "*"
                      («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                     "*"
                     `a)
                    "<"
                    (numLit "1"))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.apply
                           "apply"
                           (Term.proj
                            (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this])
                            "."
                            (fieldIdx "2")))
                          [])
                         (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `zero_lt_one)] "]"] []) [])])))
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
                  (Term.app
                   `tendsto
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [`a] [])]
                      "=>"
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                       "*"
                       `a)))
                    (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                    (Term.app
                     (Topology.Basic.term𝓝 "𝓝")
                     [(Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                       "*"
                       (numLit "0"))])]))]
                ":="
                (Term.app `tendsto_const_nhds.mul [`tendsto_id]))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`B []]
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                   " in "
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                   ", "
                   («term_<_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                     "*"
                     `a)
                    "<"
                    («term_/_» (numLit "1") "/" (numLit "2")))))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group
                          (Tactic.apply
                           "apply"
                           (Term.proj
                            (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this])
                            "."
                            (fieldIdx "2")))
                          [])
                         (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `zero_lt_one)] "]"] []) [])])))
                     [])]))))))
             [])
            (group
             (Tactic.tacticHave_
              "have"
              (Term.haveDecl
               (Term.haveIdDecl
                [`C []]
                [(Term.typeSpec
                  ":"
                  (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                   "∀ᶠ"
                   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                   " in "
                   (Topology.Basic.«term𝓝[>]_»
                    "𝓝[>] "
                    (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
                   ", "
                   («term_<_»
                    (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                    "<"
                    `a)))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic·._»
                      "·"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.filterUpwards "filter_upwards" "[" [`self_mem_nhds_within] "]" []) [])
                         (group
                          (Tactic.exact
                           "exact"
                           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `ha] [])] "=>" `ha)))
                          [])])))
                     [])]))))))
             [])
            (group
             (Tactic.rcases
              "rcases"
              [(Tactic.casesTarget
                []
                (Term.proj
                 (Term.app `C.and [(Term.app (Term.proj (Term.app `A.and [`B]) "." `filter_mono) [`inf_le_left])])
                 "."
                 `exists))]
              ["with"
               (Tactic.rcasesPat.tuple
                "⟨"
                [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                 ","
                 (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
                "⟩")])
             [])
            (group
             (Tactic.exact
              "exact"
              (Term.anonymousCtor
               "⟨"
               [`a
                ","
                (Term.proj `ha "." (fieldIdx "1"))
                ","
                (Term.proj (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")) "." `le)
                ","
                (Term.proj (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "2")) "." `le)]
               "⟩"))
             [])])))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `S
           []
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`n] [])]
             "=>"
             (Algebra.BigOperators.Basic.«term∑_in_,_»
              "∑"
              (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
              " in "
              (Term.app `Ico [(numLit "1") `n])
              ", "
              (Finset.Data.Finset.Fold.«term_*_»
               («term_^_» `a "^" `k)
               "*"
               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`IRec []]
           [(Term.typeSpec
             ":"
             (Term.forall
              "∀"
              [(Term.simpleBinder [`n] [])]
              ","
              (Term.arrow
               («term_≤_» (numLit "1") "≤" `n)
               "→"
               («term_≤_»
                (Term.app `S [`n])
                "≤"
                (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)))))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `Nat.le_induction) [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `S)] "]"] []) [])
                    (group
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] (Term.app `Ico_eq_empty_of_le [(Term.app `le_reflₓ [(numLit "1")])]))
                        ","
                        (Tactic.rwRule [] `sum_empty)]
                       "]")
                      [])
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `mul_nonneg
                       [(Term.app `add_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_one]) `apos.le]))
                     [])])))
                [])
               (group
                (Tactic.«tactic·._»
                 "·"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Tactic.intro "intro" [`n `one_le_n `hn]) [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`In []]
                        [(Term.typeSpec ":" («term_≤_» (numLit "2") "≤" (Init.Logic.«term_+_» `n "+" (numLit "1"))))]
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))))
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`Snonneg []]
                        [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `S [`n])))]
                        ":="
                        (Term.app
                         `sum_nonneg
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [(Term.simpleBinder [`x `hx] [])]
                            "=>"
                            (Term.app
                             `mul_nonneg
                             [(Term.app `pow_nonneg [`apos.le (Term.hole "_")])
                              (Term.app `norm_nonneg [(Term.hole "_")])])))]))))
                     [])
                    (group
                     (Tactic.tacticHave_
                      "have"
                      (Term.haveDecl
                       (Term.haveIdDecl
                        [`rSn []]
                        [(Term.typeSpec
                          ":"
                          («term_≤_»
                           (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                           "≤"
                           («term_/_» (numLit "1") "/" (numLit "2"))))]
                        ":="
                        (calc
                         "calc"
                         [(calcStep
                           («term_≤_»
                            (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                            "≤"
                            (Finset.Data.Finset.Fold.«term_*_»
                             `r
                             "*"
                             (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)))
                           ":="
                           (Term.app `mul_le_mul_of_nonneg_left [`hn `rpos.le]))
                          (calcStep
                           («term_≤_» (Term.hole "_") "≤" («term_/_» (numLit "1") "/" (numLit "2")))
                           ":="
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(group
                                (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `mul_assocₓ)] "]") [])
                                [])]))))]))))
                     [])
                    (group
                     (tacticCalc_
                      "calc"
                      [(calcStep
                        («term_≤_»
                         (Term.app `S [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                         "≤"
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                           "*"
                           (Algebra.BigOperators.Basic.«term∑_in_,_»
                            "∑"
                            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                            " in "
                            (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                            ", "
                            («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" `k)))))
                        ":="
                        (Term.app `radius_right_inv_pos_of_radius_pos_aux2 [`In `p `i `rpos.le `apos.le `Cpos.le `ple]))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                           "*"
                           («term_/_»
                            («term_-_»
                             («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2"))
                             "-"
                             («term_^_»
                              (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                              "^"
                              (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                            "/"
                            («term_-_»
                             (numLit "1")
                             "-"
                             (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])))))))
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
                               [(Tactic.rwRule [] (Term.app `geom_sum_Ico' [(Term.hole "_") `In]))]
                               "]")
                              [])
                             [])
                            (group
                             (Tactic.exact
                              "exact"
                              (Term.app
                               `ne_of_ltₓ
                               [(Term.app
                                 `rSn.trans_lt
                                 [(Term.byTactic
                                   "by"
                                   (Tactic.tacticSeq
                                    (Tactic.tacticSeq1Indented
                                     [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))])]))
                             [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                           "*"
                           («term_/_»
                            («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2"))
                            "/"
                            («term_/_» (numLit "1") "/" (numLit "2"))))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.applyRules
                              "apply_rules"
                              []
                              "["
                              [`add_le_add
                               ","
                               `le_reflₓ
                               ","
                               `mul_le_mul_of_nonneg_left
                               ","
                               `mul_nonneg
                               ","
                               `norm_nonneg
                               ","
                               `Cpos.le]
                              "]"
                              [])
                             [])
                            (group
                             (Tactic.refine'
                              "refine'"
                              (Term.app
                               `div_le_div
                               [(Term.app `sq_nonneg [(Term.hole "_")])
                                (Term.hole "_")
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                             [])
                            (group
                             (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `sub_le_self_iff)] "]"] [])
                             [])
                            (group
                             (Tactic.apply "apply" (Term.app `pow_nonneg [(Term.app `mul_nonneg [`rpos.le `Snonneg])]))
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                            "*"
                            `C)
                           "*"
                           («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2")))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Init.Logic.«term_+_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_»
                            (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                            "*"
                            `C)
                           "*"
                           («term_^_»
                            (Finset.Data.Finset.Fold.«term_*_»
                             `r
                             "*"
                             (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
                            "^"
                            (numLit "2")))))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.applyRules
                              "apply_rules"
                              []
                              "["
                              [`add_le_add
                               ","
                               `le_reflₓ
                               ","
                               `mul_le_mul_of_nonneg_left
                               ","
                               `mul_nonneg
                               ","
                               `norm_nonneg
                               ","
                               `Cpos.le
                               ","
                               `zero_le_two
                               ","
                               `pow_le_pow_of_le_left
                               ","
                               `rpos.le]
                              "]"
                              [])
                             [])]))))
                       (calcStep
                        («term_=_»
                         (Term.hole "_")
                         "="
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Init.Logic.«term_+_»
                           `I
                           "+"
                           (Finset.Data.Finset.Fold.«term_*_»
                            (Finset.Data.Finset.Fold.«term_*_»
                             (Finset.Data.Finset.Fold.«term_*_»
                              (Finset.Data.Finset.Fold.«term_*_»
                               (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                               "*"
                               `C)
                              "*"
                              («term_^_» `r "^" (numLit "2")))
                             "*"
                             («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                            "*"
                            `a))
                          "*"
                          `a))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                       (calcStep
                        («term_≤_»
                         (Term.hole "_")
                         "≤"
                         (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
                        ":="
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.applyRules
                              "apply_rules"
                              []
                              "["
                              [`mul_le_mul_of_nonneg_right "," `apos.le "," `add_le_add "," `le_reflₓ]
                              "]"
                              [])
                             [])]))))])
                     [])])))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl `a' [(Term.typeSpec ":" `Nnreal)] ":=" (Term.anonymousCtor "⟨" [`a "," `apos.le] "⟩"))))
        [])
       (group
        (Tactic.suffices'
         "suffices"
         [`H []]
         [(Term.typeSpec
           ":"
           («term_≤_»
            (Term.paren "(" [`a' [(Term.typeAscription ":" `Ennreal)]] ")")
            "≤"
            (Term.proj (Term.app `p.right_inv [`i]) "." `radius)))])
        [])
       (group
        (Tactic.«tactic·._»
         "·"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group
             (Tactic.«tactic·._»
              "·"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.apply "apply" (Term.app `lt_of_lt_of_leₓ [(Term.hole "_") `H])) [])
                 (group (Tactic.exactModCast "exact_mod_cast" `apos) [])])))
             [])])))
        [])
       (group
        (Tactic.apply
         "apply"
         (Term.app
          `le_radius_of_bound
          [(Term.hole "_")
           (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)
           (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))]))
        [])
       (group (Tactic.byCases' "by_cases'" [`hn ":"] («term_=_» `n "=" (numLit "0"))) [])
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
                []
                [(Term.typeSpec
                  ":"
                  («term_=_»
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
                   "="
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i (numLit "0")]) "∥")))]
                ":="
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group
                     (Tactic.«tactic_<;>_»
                      (Tactic.congr "congr" [] [])
                      "<;>"
                      (Tactic.tacticTry_
                       "try"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn)] "]") []) [])]))))
                     [])]))))))
             [])
            (group
             (Tactic.simp
              "simp"
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `this)
                ","
                (Tactic.simpLemma [] [] `norm_zero)
                ","
                (Tactic.simpLemma [] [] `zero_mul)
                ","
                (Tactic.simpLemma [] [] `right_inv_coeff_zero)]
               "]"]
              [])
             [])
            (group
             (Tactic.applyRules
              "apply_rules"
              []
              "["
              [`mul_nonneg "," `add_nonneg "," `norm_nonneg "," `zero_le_one "," `apos.le]
              "]"
              [])
             [])])))
        [])
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
                [`one_le_n []]
                [(Term.typeSpec ":" («term_≤_» (numLit "1") "≤" `n))]
                ":="
                (Term.app (Term.proj `bot_lt_iff_ne_bot "." (fieldIdx "2")) [`hn]))))
             [])
            (group
             (tacticCalc_
              "calc"
              [(calcStep
                («term_=_»
                 (Finset.Data.Finset.Fold.«term_*_»
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
                  "*"
                  («term_^_» (Init.Coe.«term↑_» "↑" `a') "^" `n))
                 "="
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_^_» `a "^" `n)
                  "*"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")))
                ":="
                (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Algebra.BigOperators.Basic.«term∑_in_,_»
                  "∑"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                  " in "
                  (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                  ", "
                  (Finset.Data.Finset.Fold.«term_*_»
                   («term_^_» `a "^" `k)
                   "*"
                   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
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
                        []
                        [(Term.typeSpec
                          ":"
                          (Term.forall
                           "∀"
                           []
                           ","
                           (Mathlib.ExtendedBinder.«term∀___,_»
                            "∀"
                            `k
                            («binderTerm∈_»
                             "∈"
                             (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                            ","
                            (Term.forall
                             "∀"
                             []
                             ","
                             («term_≤_»
                              (numLit "0")
                              "≤"
                              (Finset.Data.Finset.Fold.«term_*_»
                               («term_^_» `a "^" `k)
                               "*"
                               (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [(Term.simpleBinder [`k `hk] [])]
                          "=>"
                          (Term.app
                           `mul_nonneg
                           [(Term.app `pow_nonneg [`apos.le (Term.hole "_")])
                            (Term.app `norm_nonneg [(Term.hole "_")])]))))))
                     [])
                    (group
                     (Tactic.exact
                      "exact"
                      (Term.app
                       `single_le_sum
                       [`this
                        (Term.byTactic
                         "by"
                         (Tactic.tacticSeq
                          (Tactic.tacticSeq1Indented
                           [(group
                             (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] [])
                             [])])))]))
                     [])]))))
               (calcStep
                («term_≤_»
                 (Term.hole "_")
                 "≤"
                 (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
                ":="
                (Term.app
                 `IRec
                 [(Init.Logic.«term_+_» `n "+" (numLit "1"))
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))]))])
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
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `C)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `r)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `Cpos)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `rpos)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ple)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `C) (Lean.binderIdent `r)] ":" (Term.hole "_") ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hC)] ":" («term_<_» (numLit "0") "<" `C) ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `hr)] ":" («term_<_» (numLit "0") "<" `r) ")")])
          ","
          (Term.forall
           "∀"
           [(Term.simpleBinder [`n] [(Term.typeSpec ":" (termℕ "ℕ"))])]
           ","
           («term_≤_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p [`n]) "∥")
            "≤"
            (Finset.Data.Finset.Fold.«term_*_» `C "*" («term_^_» `r "^" `n)))))]
        [":=" [(Term.app `le_mul_pow_of_radius_pos [`p `hp])]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `I
          []
          ":="
          (Analysis.Normed.Group.Basic.«term∥_∥»
           "∥"
           (Term.paren
            "("
            [`i.symm [(Term.typeAscription ":" (Topology.Algebra.Module.«term_→L[_]_» `F " →L[" `𝕜 "] " `E))]]
            ")")
           "∥"))))
       [])
      (group
       (Tactic.obtain
        "obtain"
        [(Tactic.rcasesPatMed
          [(Tactic.rcasesPat.tuple
            "⟨"
            [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `apos)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha1)]) [])
             ","
             (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha2)]) [])]
            "⟩")])]
        [":"
         («term∃_,_»
          "∃"
          (Lean.explicitBinders
           [(Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `a)] ":" (Term.hole "_") ")")
            (Lean.bracketedExplicitBinders "(" [(Lean.binderIdent `apos)] ":" («term_<_» (numLit "0") "<" `a) ")")])
          ","
          («term_∧_»
           («term_≤_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_»
              (Finset.Data.Finset.Fold.«term_*_»
               (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I) "*" `C)
               "*"
               («term_^_» `r "^" (numLit "2")))
              "*"
              («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
             "*"
             `a)
            "≤"
            (numLit "1"))
           "∧"
           («term_≤_»
            (Finset.Data.Finset.Fold.«term_*_»
             (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
             "*"
             `a)
            "≤"
            («term_/_» (numLit "1") "/" (numLit "2")))))]
        [])
       [])
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
               []
               [(Term.typeSpec
                 ":"
                 (Term.app
                  `tendsto
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`a] [])]
                     "=>"
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_»
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                         "*"
                         `C)
                        "*"
                        («term_^_» `r "^" (numLit "2")))
                       "*"
                       («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                      "*"
                      `a)))
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                   (Term.app
                    (Topology.Basic.term𝓝 "𝓝")
                    [(Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_»
                       (Finset.Data.Finset.Fold.«term_*_»
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                         "*"
                         `C)
                        "*"
                        («term_^_» `r "^" (numLit "2")))
                       "*"
                       («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                      "*"
                      (numLit "0"))])]))]
               ":="
               (Term.app `tendsto_const_nhds.mul [`tendsto_id]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`A []]
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                  " in "
                  (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                  ", "
                  («term_<_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_»
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_» (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I) "*" `C)
                      "*"
                      («term_^_» `r "^" (numLit "2")))
                     "*"
                     («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                    "*"
                    `a)
                   "<"
                   (numLit "1"))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.apply
                          "apply"
                          (Term.proj
                           (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this])
                           "."
                           (fieldIdx "2")))
                         [])
                        (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `zero_lt_one)] "]"] []) [])])))
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
                 (Term.app
                  `tendsto
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [(Term.simpleBinder [`a] [])]
                     "=>"
                     (Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                      "*"
                      `a)))
                   (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                   (Term.app
                    (Topology.Basic.term𝓝 "𝓝")
                    [(Finset.Data.Finset.Fold.«term_*_»
                      (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                      "*"
                      (numLit "0"))])]))]
               ":="
               (Term.app `tendsto_const_nhds.mul [`tendsto_id]))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`B []]
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                  " in "
                  (Term.app (Topology.Basic.term𝓝 "𝓝") [(numLit "0")])
                  ", "
                  («term_<_»
                   (Finset.Data.Finset.Fold.«term_*_»
                    (Finset.Data.Finset.Fold.«term_*_» `r "*" (Init.Logic.«term_+_» `I "+" (numLit "1")))
                    "*"
                    `a)
                   "<"
                   («term_/_» (numLit "1") "/" (numLit "2")))))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group
                         (Tactic.apply
                          "apply"
                          (Term.proj
                           (Term.app (Term.proj `tendsto_order "." (fieldIdx "1")) [`this])
                           "."
                           (fieldIdx "2")))
                         [])
                        (group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `zero_lt_one)] "]"] []) [])])))
                    [])]))))))
            [])
           (group
            (Tactic.tacticHave_
             "have"
             (Term.haveDecl
              (Term.haveIdDecl
               [`C []]
               [(Term.typeSpec
                 ":"
                 (Filter.Order.Filter.Basic.«term∀ᶠ_in_,_»
                  "∀ᶠ"
                  (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `a)] []))
                  " in "
                  (Topology.Basic.«term𝓝[>]_»
                   "𝓝[>] "
                   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")"))
                  ", "
                  («term_<_»
                   (Term.paren "(" [(numLit "0") [(Term.typeAscription ":" (Data.Real.Basic.termℝ "ℝ"))]] ")")
                   "<"
                   `a)))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic·._»
                     "·"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(group (Tactic.filterUpwards "filter_upwards" "[" [`self_mem_nhds_within] "]" []) [])
                        (group
                         (Tactic.exact
                          "exact"
                          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`a `ha] [])] "=>" `ha)))
                         [])])))
                    [])]))))))
            [])
           (group
            (Tactic.rcases
             "rcases"
             [(Tactic.casesTarget
               []
               (Term.proj
                (Term.app `C.and [(Term.app (Term.proj (Term.app `A.and [`B]) "." `filter_mono) [`inf_le_left])])
                "."
                `exists))]
             ["with"
              (Tactic.rcasesPat.tuple
               "⟨"
               [(Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `a)]) [])
                ","
                (Tactic.rcasesPatLo (Tactic.rcasesPatMed [(Tactic.rcasesPat.one `ha)]) [])]
               "⟩")])
            [])
           (group
            (Tactic.exact
             "exact"
             (Term.anonymousCtor
              "⟨"
              [`a
               ","
               (Term.proj `ha "." (fieldIdx "1"))
               ","
               (Term.proj (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "1")) "." `le)
               ","
               (Term.proj (Term.proj (Term.proj `ha "." (fieldIdx "2")) "." (fieldIdx "2")) "." `le)]
              "⟩"))
            [])])))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `S
          []
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`n] [])]
            "=>"
            (Algebra.BigOperators.Basic.«term∑_in_,_»
             "∑"
             (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
             " in "
             (Term.app `Ico [(numLit "1") `n])
             ", "
             (Finset.Data.Finset.Fold.«term_*_»
              («term_^_» `a "^" `k)
              "*"
              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`IRec []]
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             [(Term.simpleBinder [`n] [])]
             ","
             (Term.arrow
              («term_≤_» (numLit "1") "≤" `n)
              "→"
              («term_≤_»
               (Term.app `S [`n])
               "≤"
               (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)))))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `Nat.le_induction) [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `S)] "]"] []) [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `Ico_eq_empty_of_le [(Term.app `le_reflₓ [(numLit "1")])]))
                       ","
                       (Tactic.rwRule [] `sum_empty)]
                      "]")
                     [])
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `mul_nonneg
                      [(Term.app `add_nonneg [(Term.app `norm_nonneg [(Term.hole "_")]) `zero_le_one]) `apos.le]))
                    [])])))
               [])
              (group
               (Tactic.«tactic·._»
                "·"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group (Tactic.intro "intro" [`n `one_le_n `hn]) [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`In []]
                       [(Term.typeSpec ":" («term_≤_» (numLit "2") "≤" (Init.Logic.«term_+_» `n "+" (numLit "1"))))]
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])]))))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`Snonneg []]
                       [(Term.typeSpec ":" («term_≤_» (numLit "0") "≤" (Term.app `S [`n])))]
                       ":="
                       (Term.app
                        `sum_nonneg
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [(Term.simpleBinder [`x `hx] [])]
                           "=>"
                           (Term.app
                            `mul_nonneg
                            [(Term.app `pow_nonneg [`apos.le (Term.hole "_")])
                             (Term.app `norm_nonneg [(Term.hole "_")])])))]))))
                    [])
                   (group
                    (Tactic.tacticHave_
                     "have"
                     (Term.haveDecl
                      (Term.haveIdDecl
                       [`rSn []]
                       [(Term.typeSpec
                         ":"
                         («term_≤_»
                          (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                          "≤"
                          («term_/_» (numLit "1") "/" (numLit "2"))))]
                       ":="
                       (calc
                        "calc"
                        [(calcStep
                          («term_≤_»
                           (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                           "≤"
                           (Finset.Data.Finset.Fold.«term_*_»
                            `r
                            "*"
                            (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)))
                          ":="
                          (Term.app `mul_le_mul_of_nonneg_left [`hn `rpos.le]))
                         (calcStep
                          («term_≤_» (Term.hole "_") "≤" («term_/_» (numLit "1") "/" (numLit "2")))
                          ":="
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(group
                               (tacticRwa__ "rwa" (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] `mul_assocₓ)] "]") [])
                               [])]))))]))))
                    [])
                   (group
                    (tacticCalc_
                     "calc"
                     [(calcStep
                       («term_≤_»
                        (Term.app `S [(Init.Logic.«term_+_» `n "+" (numLit "1"))])
                        "≤"
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                          "*"
                          (Algebra.BigOperators.Basic.«term∑_in_,_»
                           "∑"
                           (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                           " in "
                           (Term.app `Ico [(numLit "2") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                           ", "
                           («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" `k)))))
                       ":="
                       (Term.app `radius_right_inv_pos_of_radius_pos_aux2 [`In `p `i `rpos.le `apos.le `Cpos.le `ple]))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                          "*"
                          («term_/_»
                           («term_-_»
                            («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2"))
                            "-"
                            («term_^_»
                             (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n]))
                             "^"
                             (Init.Logic.«term_+_» `n "+" (numLit "1"))))
                           "/"
                           («term_-_»
                            (numLit "1")
                            "-"
                            (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])))))))
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
                              [(Tactic.rwRule [] (Term.app `geom_sum_Ico' [(Term.hole "_") `In]))]
                              "]")
                             [])
                            [])
                           (group
                            (Tactic.exact
                             "exact"
                             (Term.app
                              `ne_of_ltₓ
                              [(Term.app
                                `rSn.trans_lt
                                [(Term.byTactic
                                  "by"
                                  (Tactic.tacticSeq
                                   (Tactic.tacticSeq1Indented
                                    [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))])]))
                            [])]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_» `I "*" `C)
                          "*"
                          («term_/_»
                           («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2"))
                           "/"
                           («term_/_» (numLit "1") "/" (numLit "2"))))))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.applyRules
                             "apply_rules"
                             []
                             "["
                             [`add_le_add
                              ","
                              `le_reflₓ
                              ","
                              `mul_le_mul_of_nonneg_left
                              ","
                              `mul_nonneg
                              ","
                              `norm_nonneg
                              ","
                              `Cpos.le]
                             "]"
                             [])
                            [])
                           (group
                            (Tactic.refine'
                             "refine'"
                             (Term.app
                              `div_le_div
                              [(Term.app `sq_nonneg [(Term.hole "_")])
                               (Term.hole "_")
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(group (Lean.Tactic.normNum "norm_num" [] []) [])])))
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented [(group (Tactic.linarith "linarith" [] [] []) [])])))]))
                            [])
                           (group
                            (Tactic.simp "simp" [] ["only"] ["[" [(Tactic.simpLemma [] [] `sub_le_self_iff)] "]"] [])
                            [])
                           (group
                            (Tactic.apply "apply" (Term.app `pow_nonneg [(Term.app `mul_nonneg [`rpos.le `Snonneg])]))
                            [])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                           "*"
                           `C)
                          "*"
                          («term_^_» (Finset.Data.Finset.Fold.«term_*_» `r "*" (Term.app `S [`n])) "^" (numLit "2")))))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Init.Logic.«term_+_»
                         (Finset.Data.Finset.Fold.«term_*_» `I "*" `a)
                         "+"
                         (Finset.Data.Finset.Fold.«term_*_»
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                           "*"
                           `C)
                          "*"
                          («term_^_»
                           (Finset.Data.Finset.Fold.«term_*_»
                            `r
                            "*"
                            (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
                           "^"
                           (numLit "2")))))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.applyRules
                             "apply_rules"
                             []
                             "["
                             [`add_le_add
                              ","
                              `le_reflₓ
                              ","
                              `mul_le_mul_of_nonneg_left
                              ","
                              `mul_nonneg
                              ","
                              `norm_nonneg
                              ","
                              `Cpos.le
                              ","
                              `zero_le_two
                              ","
                              `pow_le_pow_of_le_left
                              ","
                              `rpos.le]
                             "]"
                             [])
                            [])]))))
                      (calcStep
                       («term_=_»
                        (Term.hole "_")
                        "="
                        (Finset.Data.Finset.Fold.«term_*_»
                         (Init.Logic.«term_+_»
                          `I
                          "+"
                          (Finset.Data.Finset.Fold.«term_*_»
                           (Finset.Data.Finset.Fold.«term_*_»
                            (Finset.Data.Finset.Fold.«term_*_»
                             (Finset.Data.Finset.Fold.«term_*_»
                              (Finset.Data.Finset.Fold.«term_*_» (numLit "2") "*" `I)
                              "*"
                              `C)
                             "*"
                             («term_^_» `r "^" (numLit "2")))
                            "*"
                            («term_^_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "^" (numLit "2")))
                           "*"
                           `a))
                         "*"
                         `a))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.Ring.tacticRing "ring") [])]))))
                      (calcStep
                       («term_≤_»
                        (Term.hole "_")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
                       ":="
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.applyRules
                             "apply_rules"
                             []
                             "["
                             [`mul_le_mul_of_nonneg_right "," `apos.le "," `add_le_add "," `le_reflₓ]
                             "]"
                             [])
                            [])]))))])
                    [])])))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl `a' [(Term.typeSpec ":" `Nnreal)] ":=" (Term.anonymousCtor "⟨" [`a "," `apos.le] "⟩"))))
       [])
      (group
       (Tactic.suffices'
        "suffices"
        [`H []]
        [(Term.typeSpec
          ":"
          («term_≤_»
           (Term.paren "(" [`a' [(Term.typeAscription ":" `Ennreal)]] ")")
           "≤"
           (Term.proj (Term.app `p.right_inv [`i]) "." `radius)))])
       [])
      (group
       (Tactic.«tactic·._»
        "·"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.«tactic·._»
             "·"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group (Tactic.apply "apply" (Term.app `lt_of_lt_of_leₓ [(Term.hole "_") `H])) [])
                (group (Tactic.exactModCast "exact_mod_cast" `apos) [])])))
            [])])))
       [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `le_radius_of_bound
         [(Term.hole "_")
          (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)
          (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`n] [])] "=>" (Term.hole "_")))]))
       [])
      (group (Tactic.byCases' "by_cases'" [`hn ":"] («term_=_» `n "=" (numLit "0"))) [])
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
               []
               [(Term.typeSpec
                 ":"
                 («term_=_»
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
                  "="
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i (numLit "0")]) "∥")))]
               ":="
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(group
                    (Tactic.«tactic_<;>_»
                     (Tactic.congr "congr" [] [])
                     "<;>"
                     (Tactic.tacticTry_
                      "try"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hn)] "]") []) [])]))))
                    [])]))))))
            [])
           (group
            (Tactic.simp
             "simp"
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `this)
               ","
               (Tactic.simpLemma [] [] `norm_zero)
               ","
               (Tactic.simpLemma [] [] `zero_mul)
               ","
               (Tactic.simpLemma [] [] `right_inv_coeff_zero)]
              "]"]
             [])
            [])
           (group
            (Tactic.applyRules
             "apply_rules"
             []
             "["
             [`mul_nonneg "," `add_nonneg "," `norm_nonneg "," `zero_le_one "," `apos.le]
             "]"
             [])
            [])])))
       [])
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
               [`one_le_n []]
               [(Term.typeSpec ":" («term_≤_» (numLit "1") "≤" `n))]
               ":="
               (Term.app (Term.proj `bot_lt_iff_ne_bot "." (fieldIdx "2")) [`hn]))))
            [])
           (group
            (tacticCalc_
             "calc"
             [(calcStep
               («term_=_»
                (Finset.Data.Finset.Fold.«term_*_»
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
                 "*"
                 («term_^_» (Init.Coe.«term↑_» "↑" `a') "^" `n))
                "="
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_^_» `a "^" `n)
                 "*"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")))
               ":="
               (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Algebra.BigOperators.Basic.«term∑_in_,_»
                 "∑"
                 (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
                 " in "
                 (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
                 ", "
                 (Finset.Data.Finset.Fold.«term_*_»
                  («term_^_» `a "^" `k)
                  "*"
                  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
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
                       []
                       [(Term.typeSpec
                         ":"
                         (Term.forall
                          "∀"
                          []
                          ","
                          (Mathlib.ExtendedBinder.«term∀___,_»
                           "∀"
                           `k
                           («binderTerm∈_»
                            "∈"
                            (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                           ","
                           (Term.forall
                            "∀"
                            []
                            ","
                            («term_≤_»
                             (numLit "0")
                             "≤"
                             (Finset.Data.Finset.Fold.«term_*_»
                              («term_^_» `a "^" `k)
                              "*"
                              (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
                       ":="
                       (Term.fun
                        "fun"
                        (Term.basicFun
                         [(Term.simpleBinder [`k `hk] [])]
                         "=>"
                         (Term.app
                          `mul_nonneg
                          [(Term.app `pow_nonneg [`apos.le (Term.hole "_")])
                           (Term.app `norm_nonneg [(Term.hole "_")])]))))))
                    [])
                   (group
                    (Tactic.exact
                     "exact"
                     (Term.app
                      `single_le_sum
                      [`this
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(group
                            (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] [])
                            [])])))]))
                    [])]))))
              (calcStep
               («term_≤_»
                (Term.hole "_")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
               ":="
               (Term.app
                `IRec
                [(Init.Logic.«term_+_» `n "+" (numLit "1"))
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))]))])
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`one_le_n []]
          [(Term.typeSpec ":" («term_≤_» (numLit "1") "≤" `n))]
          ":="
          (Term.app (Term.proj `bot_lt_iff_ne_bot "." (fieldIdx "2")) [`hn]))))
       [])
      (group
       (tacticCalc_
        "calc"
        [(calcStep
          («term_=_»
           (Finset.Data.Finset.Fold.«term_*_»
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
            "*"
            («term_^_» (Init.Coe.«term↑_» "↑" `a') "^" `n))
           "="
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `a "^" `n)
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")))
          ":="
          (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Algebra.BigOperators.Basic.«term∑_in_,_»
            "∑"
            (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
            " in "
            (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
            ", "
            (Finset.Data.Finset.Fold.«term_*_»
             («term_^_» `a "^" `k)
             "*"
             (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
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
                  []
                  [(Term.typeSpec
                    ":"
                    (Term.forall
                     "∀"
                     []
                     ","
                     (Mathlib.ExtendedBinder.«term∀___,_»
                      "∀"
                      `k
                      («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                      ","
                      (Term.forall
                       "∀"
                       []
                       ","
                       («term_≤_»
                        (numLit "0")
                        "≤"
                        (Finset.Data.Finset.Fold.«term_*_»
                         («term_^_» `a "^" `k)
                         "*"
                         (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [(Term.simpleBinder [`k `hk] [])]
                    "=>"
                    (Term.app
                     `mul_nonneg
                     [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))))))
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 `single_le_sum
                 [`this
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))]))
               [])]))))
         (calcStep
          («term_≤_»
           (Term.hole "_")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
          ":="
          (Term.app
           `IRec
           [(Init.Logic.«term_+_» `n "+" (numLit "1"))
            (Term.byTactic
             "by"
             (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))]))])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.«tactic·._»', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (tacticCalc_
   "calc"
   [(calcStep
     («term_=_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")
       "*"
       («term_^_» (Init.Coe.«term↑_» "↑" `a') "^" `n))
      "="
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" `n)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `n]) "∥")))
     ":="
     (Term.app `mul_commₓ [(Term.hole "_") (Term.hole "_")]))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Algebra.BigOperators.Basic.«term∑_in_,_»
       "∑"
       (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
       " in "
       (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
       ", "
       (Finset.Data.Finset.Fold.«term_*_»
        («term_^_» `a "^" `k)
        "*"
        (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
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
             []
             [(Term.typeSpec
               ":"
               (Term.forall
                "∀"
                []
                ","
                (Mathlib.ExtendedBinder.«term∀___,_»
                 "∀"
                 `k
                 («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
                 ","
                 (Term.forall
                  "∀"
                  []
                  ","
                  («term_≤_»
                   (numLit "0")
                   "≤"
                   (Finset.Data.Finset.Fold.«term_*_»
                    («term_^_» `a "^" `k)
                    "*"
                    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [(Term.simpleBinder [`k `hk] [])]
               "=>"
               (Term.app
                `mul_nonneg
                [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))))))
          [])
         (group
          (Tactic.exact
           "exact"
           (Term.app
            `single_le_sum
            [`this
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))]))
          [])]))))
    (calcStep
     («term_≤_»
      (Term.hole "_")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
     ":="
     (Term.app
      `IRec
      [(Init.Logic.«term_+_» `n "+" (numLit "1"))
       (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))]))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticCalc_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'calcStep', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `IRec
   [(Init.Logic.«term_+_» `n "+" (numLit "1"))
    (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.decide "decide")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.decide', expected 'Lean.Parser.Tactic.decide.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.decide "decide") [])]))) []]
 ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IRec
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_» (Term.hole "_") "≤" (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» (Init.Logic.«term_+_» `I "+" (numLit "1")) "*" `a)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Init.Logic.«term_+_» `I "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `I
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `I "+" (numLit "1")) []] ")")
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
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          []
          [(Term.typeSpec
            ":"
            (Term.forall
             "∀"
             []
             ","
             (Mathlib.ExtendedBinder.«term∀___,_»
              "∀"
              `k
              («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
              ","
              (Term.forall
               "∀"
               []
               ","
               («term_≤_»
                (numLit "0")
                "≤"
                (Finset.Data.Finset.Fold.«term_*_»
                 («term_^_» `a "^" `k)
                 "*"
                 (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`k `hk] [])]
            "=>"
            (Term.app
             `mul_nonneg
             [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))))))
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `single_le_sum
         [`this
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))]))
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
    `single_le_sum
    [`this
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))]))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.exact', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `single_le_sum
   [`this
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))])
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
     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.byTactic', expected 'Lean.Parser.Term.byTactic.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq', expected 'Lean.Parser.Tactic.tacticSeq.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeq1Indented.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simp', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«]»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `one_le_n
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
     [(group (Tactic.simp "simp" [] [] ["[" [(Tactic.simpLemma [] [] `one_le_n)] "]"] []) [])])))
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
  `single_le_sum
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
       (Term.forall
        "∀"
        []
        ","
        (Mathlib.ExtendedBinder.«term∀___,_»
         "∀"
         `k
         («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
         ","
         (Term.forall
          "∀"
          []
          ","
          («term_≤_»
           (numLit "0")
           "≤"
           (Finset.Data.Finset.Fold.«term_*_»
            («term_^_» `a "^" `k)
            "*"
            (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`k `hk] [])]
       "=>"
       (Term.app
        `mul_nonneg
        [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticHave_', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveDecl', expected 'Lean.Parser.Term.haveDecl.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.haveIdDecl', expected 'Lean.Parser.Term.haveIdDecl.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`k `hk] [])]
    "=>"
    (Term.app
     `mul_nonneg
     [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_nonneg [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) (Term.app `norm_nonneg [(Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `norm_nonneg [(Term.hole "_")])
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
  `norm_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `norm_nonneg [(Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `pow_nonneg [`apos.le (Term.hole "_")])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `apos.le
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `pow_nonneg
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `pow_nonneg [`apos.le (Term.hole "_")]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `mul_nonneg
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   (Mathlib.ExtendedBinder.«term∀___,_»
    "∀"
    `k
    («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
    ","
    (Term.forall
     "∀"
     []
     ","
     («term_≤_»
      (numLit "0")
      "≤"
      (Finset.Data.Finset.Fold.«term_*_»
       («term_^_» `a "^" `k)
       "*"
       (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.ExtendedBinder.«term∀___,_»
   "∀"
   `k
   («binderTerm∈_» "∈" (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))]))
   ","
   (Term.forall
    "∀"
    []
    ","
    («term_≤_»
     (numLit "0")
     "≤"
     (Finset.Data.Finset.Fold.«term_*_»
      («term_^_» `a "^" `k)
      "*"
      (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Mathlib.ExtendedBinder.«term∀___,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   []
   ","
   («term_≤_»
    (numLit "0")
    "≤"
    (Finset.Data.Finset.Fold.«term_*_»
     («term_^_» `a "^" `k)
     "*"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.forall', expected 'Lean.Parser.Term.forall.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (numLit "0")
   "≤"
   (Finset.Data.Finset.Fold.«term_*_»
    («term_^_» `a "^" `k)
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_^_» `a "^" `k)
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.right_inv [`i `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» `a "^" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `a "^" `k) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (numLit "0")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«binderTerm∈_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ico
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_≤_»
   (Term.hole "_")
   "≤"
   (Algebra.BigOperators.Basic.«term∑_in_,_»
    "∑"
    (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
    " in "
    (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
    ", "
    (Finset.Data.Finset.Fold.«term_*_»
     («term_^_» `a "^" `k)
     "*"
     (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_≤_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Algebra.BigOperators.Basic.«term∑_in_,_»
   "∑"
   (Lean.explicitBinders (Lean.unbracketedExplicitBinders [(Lean.binderIdent `k)] []))
   " in "
   (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
   ", "
   (Finset.Data.Finset.Fold.«term_*_»
    («term_^_» `a "^" `k)
    "*"
    (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Algebra.BigOperators.Basic.«term∑_in_,_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_»
   («term_^_» `a "^" `k)
   "*"
   (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Analysis.Normed.Group.Basic.«term∥_∥» "∥" (Term.app `p.right_inv [`i `k]) "∥")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Analysis.Normed.Group.Basic.«term∥_∥»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `p.right_inv [`i `k])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `i
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `p.right_inv
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  («term_^_» `a "^" `k)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_^_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `k
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 80 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 80, term))
  `a
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 81 >? 1024, (none, [anonymous]) <=? (some 80, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 80, (some 80, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(«term_^_» `a "^" `k) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Ico [(numLit "1") (Init.Logic.«term_+_» `n "+" (numLit "1"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Logic.«term_+_» `n "+" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Logic.«term_+_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `n
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Init.Logic.«term_+_» `n "+" (numLit "1")) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Ico
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
    If a a formal multilinear series has a positive radius of convergence, then its right inverse
    also has a positive radius of convergence. -/
  theorem
    radius_right_inv_pos_of_radius_pos
    ( p : FormalMultilinearSeries 𝕜 E F ) ( i : E ≃L[ 𝕜 ] F ) ( hp : 0 < p.radius ) : 0 < p.right_inv i . radius
    :=
      by
        obtain
            ⟨ C , r , Cpos , rpos , ple ⟩
            : ∃ ( C r : _ ) ( hC : 0 < C ) ( hr : 0 < r ) , ∀ n : ℕ , ∥ p n ∥ ≤ C * r ^ n
            := le_mul_pow_of_radius_pos p hp
          let I := ∥ ( i.symm : F →L[ 𝕜 ] E ) ∥
          obtain
            ⟨ a , apos , ha1 , ha2 ⟩
            : ∃ ( a : _ ) ( apos : 0 < a ) , 2 * I * C * r ^ 2 * I + 1 ^ 2 * a ≤ 1 ∧ r * I + 1 * a ≤ 1 / 2
          ·
            have
                : tendsto fun a => 2 * I * C * r ^ 2 * I + 1 ^ 2 * a 𝓝 0 𝓝 2 * I * C * r ^ 2 * I + 1 ^ 2 * 0
                  :=
                  tendsto_const_nhds.mul tendsto_id
              have
                A
                  : ∀ᶠ a in 𝓝 0 , 2 * I * C * r ^ 2 * I + 1 ^ 2 * a < 1
                  :=
                  by · apply tendsto_order . 1 this . 2 simp [ zero_lt_one ]
              have : tendsto fun a => r * I + 1 * a 𝓝 0 𝓝 r * I + 1 * 0 := tendsto_const_nhds.mul tendsto_id
              have B : ∀ᶠ a in 𝓝 0 , r * I + 1 * a < 1 / 2 := by · apply tendsto_order . 1 this . 2 simp [ zero_lt_one ]
              have
                C
                  : ∀ᶠ a in 𝓝[>] ( 0 : ℝ ) , ( 0 : ℝ ) < a
                  :=
                  by · filter_upwards [ self_mem_nhds_within ] exact fun a ha => ha
              rcases C.and A.and B . filter_mono inf_le_left . exists with ⟨ a , ha ⟩
              exact ⟨ a , ha . 1 , ha . 2 . 1 . le , ha . 2 . 2 . le ⟩
          let S := fun n => ∑ k in Ico 1 n , a ^ k * ∥ p.right_inv i k ∥
          have
            IRec
              : ∀ n , 1 ≤ n → S n ≤ I + 1 * a
              :=
              by
                apply Nat.le_induction
                  ·
                    simp only [ S ]
                      rw [ Ico_eq_empty_of_le le_reflₓ 1 , sum_empty ]
                      exact mul_nonneg add_nonneg norm_nonneg _ zero_le_one apos.le
                  ·
                    intro n one_le_n hn
                      have In : 2 ≤ n + 1 := by linarith
                      have Snonneg : 0 ≤ S n := sum_nonneg fun x hx => mul_nonneg pow_nonneg apos.le _ norm_nonneg _
                      have
                        rSn
                          : r * S n ≤ 1 / 2
                          :=
                          calc
                            r * S n ≤ r * I + 1 * a := mul_le_mul_of_nonneg_left hn rpos.le
                              _ ≤ 1 / 2 := by rwa [ ← mul_assocₓ ]
                      calc
                        S n + 1 ≤ I * a + I * C * ∑ k in Ico 2 n + 1 , r * S n ^ k
                            :=
                            radius_right_inv_pos_of_radius_pos_aux2 In p i rpos.le apos.le Cpos.le ple
                          _ = I * a + I * C * r * S n ^ 2 - r * S n ^ n + 1 / 1 - r * S n
                            :=
                            by rw [ geom_sum_Ico' _ In ] exact ne_of_ltₓ rSn.trans_lt by norm_num
                          _ ≤ I * a + I * C * r * S n ^ 2 / 1 / 2
                            :=
                            by
                              apply_rules
                                  [
                                  add_le_add , le_reflₓ , mul_le_mul_of_nonneg_left , mul_nonneg , norm_nonneg , Cpos.le
                                  ]
                                refine' div_le_div sq_nonneg _ _ by norm_num by linarith
                                simp only [ sub_le_self_iff ]
                                apply pow_nonneg mul_nonneg rpos.le Snonneg
                          _ = I * a + 2 * I * C * r * S n ^ 2 := by ring
                          _ ≤ I * a + 2 * I * C * r * I + 1 * a ^ 2
                            :=
                            by
                              apply_rules
                                [
                                add_le_add
                                  ,
                                  le_reflₓ
                                  ,
                                  mul_le_mul_of_nonneg_left
                                  ,
                                  mul_nonneg
                                  ,
                                  norm_nonneg
                                  ,
                                  Cpos.le
                                  ,
                                  zero_le_two
                                  ,
                                  pow_le_pow_of_le_left
                                  ,
                                  rpos.le
                                ]
                          _ = I + 2 * I * C * r ^ 2 * I + 1 ^ 2 * a * a := by ring
                          _ ≤ I + 1 * a
                            :=
                            by apply_rules [ mul_le_mul_of_nonneg_right , apos.le , add_le_add , le_reflₓ ]
          let a' : Nnreal := ⟨ a , apos.le ⟩
          suffices H : ( a' : Ennreal ) ≤ p.right_inv i . radius
          · · apply lt_of_lt_of_leₓ _ H exact_mod_cast apos
          apply le_radius_of_bound _ I + 1 * a fun n => _
          by_cases' hn : n = 0
          ·
            have : ∥ p.right_inv i n ∥ = ∥ p.right_inv i 0 ∥ := by congr <;> try rw [ hn ]
              simp only [ this , norm_zero , zero_mul , right_inv_coeff_zero ]
              apply_rules [ mul_nonneg , add_nonneg , norm_nonneg , zero_le_one , apos.le ]
          ·
            have one_le_n : 1 ≤ n := bot_lt_iff_ne_bot . 2 hn
              calc
                ∥ p.right_inv i n ∥ * ↑ a' ^ n = a ^ n * ∥ p.right_inv i n ∥ := mul_commₓ _ _
                  _ ≤ ∑ k in Ico 1 n + 1 , a ^ k * ∥ p.right_inv i k ∥
                    :=
                    by
                      have
                          : ∀ , ∀ k ∈ Ico 1 n + 1 , ∀ , 0 ≤ a ^ k * ∥ p.right_inv i k ∥
                            :=
                            fun k hk => mul_nonneg pow_nonneg apos.le _ norm_nonneg _
                        exact single_le_sum this by simp [ one_le_n ]
                  _ ≤ I + 1 * a := IRec n + 1 by decide

end FormalMultilinearSeries

