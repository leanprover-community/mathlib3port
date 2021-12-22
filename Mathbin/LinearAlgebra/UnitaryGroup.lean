import Mathbin.LinearAlgebra.Matrix.ToLin
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse

/-!
# The Unitary Group

This file defines elements of the unitary group `unitary_group n α`, where `α` is a `star_ring`.
This consists of all `n` by `n` matrices with entries in `α` such that the star-transpose is its
inverse. In addition, we define the group structure on `unitary_group n α`, and the embedding into
the general linear group `general_linear_group α (n → α)`.

We also define the orthogonal group `orthogonal_group n β`, where `β` is a `comm_ring`.

## Main Definitions

 * `matrix.unitary_group` is the type of matrices where the star-transpose is the inverse
 * `matrix.unitary_group.group` is the group structure (under multiplication)
 * `matrix.unitary_group.embedding_GL` is the embedding `unitary_group n α → GLₙ(α)`
 * `matrix.orthogonal_group` is the type of matrices where the transpose is the inverse

## References

 * https://en.wikipedia.org/wiki/Unitary_group

## Tags

matrix group, group, unitary group, orthogonal group

-/


universe u v

section

variable (M : Type v) [Monoidₓ M] [StarMonoid M]

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers
  [(Command.docComment
    "/--"
    "\nIn a `star_monoid M`, `unitary_submonoid M` is the submonoid consisting of all the elements of\n`M` such that `star A * A = 1`.\n-/")]
  []
  []
  []
  []
  [])
 (Command.def
  "def"
  (Command.declId `unitarySubmonoid [])
  (Command.optDeclSig [] [(Term.typeSpec ":" (Term.app `Submonoid [`M]))])
  (Command.declValSimple
   ":="
   (Term.structInst
    "{"
    []
    [(group
      (Term.structInstField
       (Term.structInstLVal `Carrier [])
       ":="
       (Set.«term{_|_}»
        "{"
        `A
        "|"
        («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1"))
        "}"))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `one_mem' [])
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))
      [","])
     (group
      (Term.structInstField
       (Term.structInstLVal `mul_mem' [])
       ":="
       (Term.fun
        "fun"
        (Term.basicFun
         [(Term.simpleBinder [`A `B] [])
          (Term.simpleBinder
           [`hA]
           [(Term.typeSpec
             ":"
             («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1")))])
          (Term.simpleBinder
           [`hB]
           [(Term.typeSpec
             ":"
             («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B) "=" (numLit "1")))])]
         "=>"
         (Term.show
          "show"
          («term_=_»
           (Finset.Data.Finset.Fold.«term_*_»
            (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
            "*"
            (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
           "="
           (numLit "1"))
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group
               (tacticRwa__
                "rwa"
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `star_mul)
                  ","
                  (Tactic.rwRule ["←"] `mul_assocₓ)
                  ","
                  (Tactic.rwRule [] (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A]))
                  ","
                  (Tactic.rwRule [] `hA)
                  ","
                  (Tactic.rwRule [] `mul_oneₓ)]
                 "]")
                [])
               [])])))))))
      [])]
    (Term.optEllipsis [])
    []
    "}")
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
  (Term.structInst
   "{"
   []
   [(group
     (Term.structInstField
      (Term.structInstLVal `Carrier [])
      ":="
      (Set.«term{_|_}»
       "{"
       `A
       "|"
       («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1"))
       "}"))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `one_mem' [])
      ":="
      (Term.byTactic "by" (Tactic.tacticSeq (Tactic.tacticSeq1Indented [(group (Tactic.simp "simp" [] [] [] []) [])]))))
     [","])
    (group
     (Term.structInstField
      (Term.structInstLVal `mul_mem' [])
      ":="
      (Term.fun
       "fun"
       (Term.basicFun
        [(Term.simpleBinder [`A `B] [])
         (Term.simpleBinder
          [`hA]
          [(Term.typeSpec
            ":"
            («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1")))])
         (Term.simpleBinder
          [`hB]
          [(Term.typeSpec
            ":"
            («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B) "=" (numLit "1")))])]
        "=>"
        (Term.show
         "show"
         («term_=_»
          (Finset.Data.Finset.Fold.«term_*_»
           (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
           "*"
           (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
          "="
          (numLit "1"))
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(group
              (tacticRwa__
               "rwa"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `star_mul)
                 ","
                 (Tactic.rwRule ["←"] `mul_assocₓ)
                 ","
                 (Tactic.rwRule [] (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A]))
                 ","
                 (Tactic.rwRule [] `hA)
                 ","
                 (Tactic.rwRule [] `mul_oneₓ)]
                "]")
               [])
              [])])))))))
     [])]
   (Term.optEllipsis [])
   []
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.structInst.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.optEllipsis', expected 'Lean.Parser.Term.optEllipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`A `B] [])
     (Term.simpleBinder
      [`hA]
      [(Term.typeSpec
        ":"
        («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1")))])
     (Term.simpleBinder
      [`hB]
      [(Term.typeSpec
        ":"
        («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B) "=" (numLit "1")))])]
    "=>"
    (Term.show
     "show"
     («term_=_»
      (Finset.Data.Finset.Fold.«term_*_»
       (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
       "*"
       (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
      "="
      (numLit "1"))
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group
          (tacticRwa__
           "rwa"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `star_mul)
             ","
             (Tactic.rwRule ["←"] `mul_assocₓ)
             ","
             (Tactic.rwRule [] (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A]))
             ","
             (Tactic.rwRule [] `hA)
             ","
             (Tactic.rwRule [] `mul_oneₓ)]
            "]")
           [])
          [])]))))))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.fun.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.basicFun.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.show
   "show"
   («term_=_»
    (Finset.Data.Finset.Fold.«term_*_»
     (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
     "*"
     (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
    "="
    (numLit "1"))
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (tacticRwa__
         "rwa"
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] `star_mul)
           ","
           (Tactic.rwRule ["←"] `mul_assocₓ)
           ","
           (Tactic.rwRule [] (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A]))
           ","
           (Tactic.rwRule [] `hA)
           ","
           (Tactic.rwRule [] `mul_oneₓ)]
          "]")
         [])
        [])]))))
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
  (tacticRwa__
   "rwa"
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `star_mul)
     ","
     (Tactic.rwRule ["←"] `mul_assocₓ)
     ","
     (Tactic.rwRule [] (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A]))
     ","
     (Tactic.rwRule [] `hA)
     ","
     (Tactic.rwRule [] `mul_oneₓ)]
    "]")
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'tacticRwa__', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_oneₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hA
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `mul_assocₓ [(Term.hole "_") (Term.hole "_") `A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
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
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `mul_assocₓ
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«←»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.rwRule', expected 'sepBy.antiquot_scope'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `star_mul
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, [anonymous]))
  («term_=_»
   (Finset.Data.Finset.Fold.«term_*_»
    (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
    "*"
    (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
   "="
   (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_»
   (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
   "*"
   (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `A "*" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `star [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B)])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Finset.Data.Finset.Fold.«term_*_» `A "*" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `star
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_»
   (Term.app `star [(Term.paren "(" [(Finset.Data.Finset.Fold.«term_*_» `A "*" `B) []] ")")])
   "*"
   (Finset.Data.Finset.Fold.«term_*_» `A "*" `B))
  []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1022, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
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
  («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B) "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `B
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `star [`B])
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
  `star
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`B]) "*" `B) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.typeSpec', expected 'Lean.Parser.Term.typeSpec.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, [anonymous]))
  («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `star [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `star
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (some 1023, [anonymous])
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
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
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstLVal', expected 'Lean.Parser.Term.structInstLVal.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'group', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«,»', expected 'optional.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstField.antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Set.«term{_|_}»
   "{"
   `A
   "|"
   («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1"))
   "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Set.«term{_|_}»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_» (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) "=" (numLit "1"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind '«term_=_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (numLit "1")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'numLit', expected 'numLit.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
  (Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Finset.Data.Finset.Fold.«term_*_»', expected 'antiquot'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.app `star [`A])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'many.antiquot_scope'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis.antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `A
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `star
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'antiquot'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'ident.antiquot'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 0, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Finset.Data.Finset.Fold.«term_*_» (Term.app `star [`A]) "*" `A) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
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
    In a `star_monoid M`, `unitary_submonoid M` is the submonoid consisting of all the elements of
    `M` such that `star A * A = 1`.
    -/
  def
    unitarySubmonoid
    : Submonoid M
    :=
      {
        Carrier := { A | star A * A = 1 } ,
          one_mem' := by simp ,
          mul_mem'
            :=
            fun
              A B hA : star A * A = 1 hB : star B * B = 1
                =>
                show star A * B * A * B = 1 by rwa [ star_mul , ← mul_assocₓ , mul_assocₓ _ _ A , hA , mul_oneₓ ]
        }

end

namespace Matrix

open LinearMap

open_locale Matrix

section

variable (n : Type u) [DecidableEq n] [Fintype n]

variable (α : Type v) [CommRingₓ α] [StarRing α]

-- ././Mathport/Syntax/Translate/Basic.lean:833:9: unsupported derive handler monoid
/-- 
`unitary_group n` is the group of `n` by `n` matrices where the star-transpose is the inverse.
-/
def unitary_group : Type _ :=
  unitarySubmonoid (Matrix n n α)deriving [anonymous]

end

variable {n : Type u} [DecidableEq n] [Fintype n]

variable {α : Type v} [CommRingₓ α] [StarRing α]

namespace unitarySubmonoid

theorem star_mem {A : Matrix n n α} (h : A ∈ unitarySubmonoid (Matrix n n α)) :
    star A ∈ unitarySubmonoid (Matrix n n α) :=
  mul_eq_one_comm.mp $ (star_star A).symm ▸ h

@[simp]
theorem star_mem_iff {A : Matrix n n α} :
    star A ∈ unitarySubmonoid (Matrix n n α) ↔ A ∈ unitarySubmonoid (Matrix n n α) :=
  ⟨fun ha => star_star A ▸ star_mem ha, star_mem⟩

end unitarySubmonoid

namespace UnitaryGroup

instance coe_matrix : Coe (unitary_group n α) (Matrix n n α) :=
  ⟨Subtype.val⟩

-- failed to format: format: uncaught backtrack exception
instance coe_fun : CoeFun ( unitary_group n α ) fun _ => n → n → α where coe A := A.val

/-- 
`to_lin' A` is matrix multiplication of vectors by `A`, as a linear map.

After the group structure on `unitary_group n` is defined,
we show in `to_linear_equiv` that this gives a linear equivalence.
-/
def to_lin' (A : unitary_group n α) :=
  Matrix.toLin' A

theorem ext_iff (A B : unitary_group n α) : A = B ↔ ∀ i j, A i j = B i j :=
  Subtype.ext_iff_val.trans ⟨fun h i j => congr_funₓ (congr_funₓ h i) j, Matrix.ext⟩

@[ext]
theorem ext (A B : unitary_group n α) : (∀ i j, A i j = B i j) → A = B :=
  (unitary_group.ext_iff A B).mpr

instance : HasInv (unitary_group n α) :=
  ⟨fun A => ⟨star A.1, unitary_submonoid.star_mem_iff.mpr A.2⟩⟩

-- failed to format: format: uncaught backtrack exception
instance
  : StarMonoid ( unitary_group n α )
  where
    star A := ⟨ star A . 1 , unitary_submonoid.star_mem A . 2 ⟩
      star_involutive A := Subtype.ext $ star_star A . 1
      star_mul A B := Subtype.ext $ star_mul A . 1 B . 1

@[simp]
theorem star_mul_self (A : unitary_group n α) : star A ⬝ A = 1 :=
  A.2

instance : Inhabited (unitary_group n α) :=
  ⟨1⟩

section CoeLemmas

variable (A B : unitary_group n α)

@[simp]
theorem inv_val : ↑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem inv_apply : ⇑A⁻¹ = (star A : Matrix n n α) :=
  rfl

@[simp]
theorem mul_val : (↑A*B) = A ⬝ B :=
  rfl

@[simp]
theorem mul_apply : (⇑A*B) = A ⬝ B :=
  rfl

@[simp]
theorem one_val : ↑(1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem one_apply : ⇑(1 : unitary_group n α) = (1 : Matrix n n α) :=
  rfl

@[simp]
theorem to_lin'_mul : to_lin' (A*B) = (to_lin' A).comp (to_lin' B) :=
  Matrix.to_lin'_mul A B

@[simp]
theorem to_lin'_one : to_lin' (1 : unitary_group n α) = LinearMap.id :=
  Matrix.to_lin'_one

end CoeLemmas

instance : Groupₓ (unitary_group n α) :=
  { unitary_group.has_inv, unitary_group.monoid n α with mul_left_inv := fun A => Subtype.eq A.2 }

/--  `to_linear_equiv A` is matrix multiplication of vectors by `A`, as a linear equivalence. -/
def to_linear_equiv (A : unitary_group n α) : (n → α) ≃ₗ[α] n → α :=
  { Matrix.toLin' A with invFun := A⁻¹.toLin',
    left_inv := fun x =>
      calc A⁻¹.toLin'.comp A.to_lin' x = (A⁻¹*A).toLin' x := by
        rw [← to_lin'_mul]
        _ = x := by
        rw [mul_left_invₓ, to_lin'_one, id_apply]
        ,
    right_inv := fun x =>
      calc A.to_lin'.comp A⁻¹.toLin' x = (A*A⁻¹).toLin' x := by
        rw [← to_lin'_mul]
        _ = x := by
        rw [mul_right_invₓ, to_lin'_one, id_apply]
         }

/--  `to_GL` is the map from the unitary group to the general linear group -/
def to_GL (A : unitary_group n α) : general_linear_group α (n → α) :=
  general_linear_group.of_linear_equiv (to_linear_equiv A)

theorem coe_to_GL (A : unitary_group n α) : ↑to_GL A = A.to_lin' :=
  rfl

@[simp]
theorem to_GL_one : to_GL (1 : unitary_group n α) = 1 := by
  ext1 v i
  rw [coe_to_GL, to_lin'_one]
  rfl

@[simp]
theorem to_GL_mul (A B : unitary_group n α) : to_GL (A*B) = to_GL A*to_GL B := by
  ext1 v i
  rw [coe_to_GL, to_lin'_mul]
  rfl

/--  `unitary_group.embedding_GL` is the embedding from `unitary_group n α`
to `general_linear_group n α`. -/
def embedding_GL : unitary_group n α →* general_linear_group α (n → α) :=
  ⟨fun A => to_GL A, by
    simp , by
    simp ⟩

end UnitaryGroup

section OrthogonalGroup

variable (β : Type v) [CommRingₓ β]

attribute [local instance] starRingOfComm

/-- 
`orthogonal_group n` is the group of `n` by `n` matrices where the transpose is the inverse.
-/
abbrev orthogonal_group :=
  unitary_group n β

end OrthogonalGroup

end Matrix

