/-
Copyright (c) 2020 Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Patrick Lutz
-/
import Mathbin.FieldTheory.Normal
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.FieldTheory.Fixed
import Mathbin.RingTheory.PowerBasis
import Mathbin.GroupTheory.GroupAction.FixingSubgroup

/-!
# Galois Extensions

In this file we define Galois extensions as extensions which are both separable and normal.

## Main definitions

- `is_galois F E` where `E` is an extension of `F`
- `fixed_field H` where `H : subgroup (E ≃ₐ[F] E)`
- `fixing_subgroup K` where `K : intermediate_field F E`
- `galois_correspondence` where `E/F` is finite dimensional and Galois

## Main results

- `intermediate_field.fixing_subgroup_fixed_field` : If `E/F` is finite dimensional (but not
  necessarily Galois) then `fixing_subgroup (fixed_field H) = H`
- `intermediate_field.fixed_field_fixing_subgroup`: If `E/F` is finite dimensional and Galois
  then `fixed_field (fixing_subgroup K) = K`

Together, these two results prove the Galois correspondence.

- `is_galois.tfae` : Equivalent characterizations of a Galois extension of finite degree
-/


open Polynomial

open FiniteDimensional AlgEquiv

section

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

/-- A field extension E/F is galois if it is both separable and normal. Note that in mathlib
a separable extension of fields is by definition algebraic. -/
class IsGalois : Prop where
  [to_is_separable : IsSeparable F E]
  [to_normal : Normal F E]

variable {F E}

theorem is_galois_iff : IsGalois F E ↔ IsSeparable F E ∧ Normal F E :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => { to_is_separable := h.1, to_normal := h.2 }⟩

attribute [instance] IsGalois.to_is_separable IsGalois.to_normal

-- see Note [lower instance priority]
variable (F E)

namespace IsGalois

instance self : IsGalois F F :=
  ⟨⟩

variable (F) {E}

theorem integral [IsGalois F E] (x : E) : IsIntegral F x :=
  Normal.is_integral' x

theorem separable [IsGalois F E] (x : E) : (minpoly F x).Separable :=
  IsSeparable.separable F x

theorem splits [IsGalois F E] (x : E) : (minpoly F x).Splits (algebraMap F E) :=
  Normal.splits' x

variable (F E)

instance of_fixed_field (G : Type _) [Groupₓ G] [Fintype G] [MulSemiringAction G E] :
    IsGalois (FixedPoints.subfield G E) E :=
  ⟨⟩

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `IntermediateField.AdjoinSimple.card_aut_eq_finrank [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.implicitBinder "{" [`α] [":" `E] "}")
    (Term.explicitBinder "(" [`hα] [":" (Term.app `IsIntegral [`F `α])] [] ")")
    (Term.explicitBinder "(" [`h_sep] [":" (Term.proj (Term.app `minpoly [`F `α]) "." `Separable)] [] ")")
    (Term.explicitBinder
     "("
     [`h_splits]
     [":"
      (Term.app
       (Term.proj (Term.app `minpoly [`F `α]) "." `Splits)
       [(Term.app
         `algebraMap
         [`F
          (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
           `F
           "⟮"
           (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
           "⟯")])])]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Fintype.card
      [(Algebra.Algebra.Basic.«term_≃ₐ[_]_»
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")
        " ≃ₐ["
        `F
        "] "
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `F
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯"))])
     "="
     (Term.app
      `finrank
      [`F
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")]))))
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
          (Term.letPatDecl
           (Lean.termThis "this")
           []
           [(Term.typeSpec
             ":"
             (Term.app
              `Fintype
              [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                " →ₐ["
                `F
                "] "
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `F
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯"))]))]
           ":="
           (Term.app `IntermediateField.fintypeOfAlgHomAdjoinIntegral [`F `hα]))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `IntermediateField.adjoin.finrank [`hα]))] "]")
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule ["←"] (Term.app `IntermediateField.card_alg_hom_adjoin_integral [`F `hα `h_sep `h_splits]))]
          "]")
         [])
        [])
       (group
        (Tactic.exact
         "exact"
         (Term.app
          `Fintype.card_congr
          [(Term.app
            `algEquivEquivAlgHom
            [`F
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")])]))
        [])])))
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
     [(group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letPatDecl
          (Lean.termThis "this")
          []
          [(Term.typeSpec
            ":"
            (Term.app
             `Fintype
             [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `F
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")
               " →ₐ["
               `F
               "] "
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `F
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯"))]))]
          ":="
          (Term.app `IntermediateField.fintypeOfAlgHomAdjoinIntegral [`F `hα]))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `IntermediateField.adjoin.finrank [`hα]))] "]")
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule ["←"] (Term.app `IntermediateField.card_alg_hom_adjoin_integral [`F `hα `h_sep `h_splits]))]
         "]")
        [])
       [])
      (group
       (Tactic.exact
        "exact"
        (Term.app
         `Fintype.card_congr
         [(Term.app
           `algEquivEquivAlgHom
           [`F
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `F
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")])]))
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Fintype.card_congr
    [(Term.app
      `algEquivEquivAlgHom
      [`F
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `F
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Fintype.card_congr
   [(Term.app
     `algEquivEquivAlgHom
     [`F
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `algEquivEquivAlgHom
   [`F
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `F
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  IntermediateField.AdjoinSimple.card_aut_eq_finrank
  [ FiniteDimensional F E ]
      { α : E }
      ( hα : IsIntegral F α )
      ( h_sep : minpoly F α . Separable )
      (
        h_splits
        :
          minpoly F α . Splits
            algebraMap F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        )
    :
      Fintype.card
          F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
            ≃ₐ[
            F
            ]
            F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
        =
        finrank F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  :=
    by
      let
          this
            :
              Fintype
                F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                  →ₐ[
                  F
                  ]
                  F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
            :=
            IntermediateField.fintypeOfAlgHomAdjoinIntegral F hα
        rw [ IntermediateField.adjoin.finrank hα ]
        rw [ ← IntermediateField.card_alg_hom_adjoin_integral F hα h_sep h_splits ]
        exact
          Fintype.card_congr
            algEquivEquivAlgHom F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `card_aut_eq_finrank [])
  (Command.declSig
   [(Term.instBinder "[" [] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.instBinder "[" [] (Term.app `IsGalois [`F `E]) "]")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app `Fintype.card [(Algebra.Algebra.Basic.«term_≃ₐ[_]_» `E " ≃ₐ[" `F "] " `E)])
     "="
     (Term.app `finrank [`F `E]))))
  (Command.declValSimple
   ":="
   (Term.byTactic
    "by"
    (Tactic.tacticSeq
     (Tactic.tacticSeq1Indented
      [(group
        (Tactic.cases'
         "cases'"
         [(Tactic.casesTarget [] (Term.app `Field.exists_primitive_element [`F `E]))]
         []
         ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hα)]])
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `iso
           []
           [(Term.typeSpec
             ":"
             (Algebra.Algebra.Basic.«term_≃ₐ[_]_»
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")
              " ≃ₐ["
              `F
              "] "
              `E))]
           ":="
           (Term.structInst
            "{"
            []
            [(group
              (Term.structInstField
               (Term.structInstLVal `toFun [])
               ":="
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Term.proj `e "." `val))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `invFun [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [`e] [])]
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [`e
                   ","
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hα)] "]") []) [])
                       (group (Tactic.exact "exact" `IntermediateField.mem_top) [])])))]
                  "⟩"))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `left_inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_")] [])]
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                     (group (Tactic.tacticRfl "rfl") [])]))))))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `right_inv [])
               ":="
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl)))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `map_mul' [])
               ":="
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `map_add' [])
               ":="
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))
              [","])
             (group
              (Term.structInstField
               (Term.structInstLVal `commutes' [])
               ":="
               (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl)))
              [])]
            (Term.optEllipsis [])
            []
            "}"))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`H []]
           [(Term.typeSpec ":" (Term.app `IsIntegral [`F `α]))]
           ":="
           (Term.app `IsGalois.integral [`F `α]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_sep []]
           [(Term.typeSpec ":" (Term.proj (Term.app `minpoly [`F `α]) "." `Separable))]
           ":="
           (Term.app `IsGalois.separable [`F `α]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h_splits []]
           [(Term.typeSpec
             ":"
             (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `Splits) [(Term.app `algebraMap [`F `E])]))]
           ":="
           (Term.app `IsGalois.splits [`F `α]))))
        [])
       (group
        (Tactic.replace'
         "replace"
         [`h_splits []]
         [(Term.typeSpec
           ":"
           (Term.app
            `Polynomial.Splits
            [(Term.app
              `algebraMap
              [`F
               (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                `F
                "⟮"
                (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                "⟯")])
             (Term.app `minpoly [`F `α])]))])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.tacticHave_
            "have"
            (Term.haveDecl
             (Term.haveIdDecl
              [`p []]
              [(Term.typeSpec
                ":"
                («term_=_»
                 (Term.app `iso.symm.to_alg_hom.to_ring_hom.comp [(Term.app `algebraMap [`F `E])])
                 "="
                 (Term.app
                  `algebraMap
                  [`F
                   (Init.Coe.«term↥_»
                    "↥"
                    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                     `F
                     "⟮"
                     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                     "⟯"))])))]
              ":="
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                  (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
           [])
          (group
           (Mathlib.Tactic.tacticSimpa!?_
            "simpa"
            []
            []
            (Mathlib.Tactic.simpaArgsRest
             []
             []
             []
             [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `p)] "]")]
             []
             [(Tactic.usingArg
               "using"
               (Term.app
                `Polynomial.splits_comp_of_splits
                [(Term.app `algebraMap [`F `E]) `iso.symm.to_alg_hom.to_ring_hom `h_splits]))]))
           [])])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `LinearEquiv.finrank_eq [`iso.to_linear_equiv]))] "]")
         [])
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            ["←"]
            (Term.app `intermediate_field.adjoin_simple.card_aut_eq_finrank [`F `E `H `h_sep `h_splits]))]
          "]")
         [])
        [])
       (group (Tactic.apply "apply" `Fintype.card_congr) [])
       (group
        (Tactic.apply
         "apply"
         (Term.app
          `Equivₓ.mk
          [(Term.fun
            "fun"
            (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])))
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`ϕ] [])]
             "=>"
             (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])))]))
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.intro "intro" [`ϕ]) [])
          (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
          (group
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `apply_symm_apply)] "]"]
            [])
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group (Tactic.intro "intro" [`ϕ]) [])
          (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
          (group
           (Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `symm_apply_apply)] "]"]
            [])
           [])])
        [])])))
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
     [(group
       (Tactic.cases'
        "cases'"
        [(Tactic.casesTarget [] (Term.app `Field.exists_primitive_element [`F `E]))]
        []
        ["with" [(Lean.binderIdent `α) (Lean.binderIdent `hα)]])
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `iso
          []
          [(Term.typeSpec
            ":"
            (Algebra.Algebra.Basic.«term_≃ₐ[_]_»
             (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
              `F
              "⟮"
              (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
              "⟯")
             " ≃ₐ["
             `F
             "] "
             `E))]
          ":="
          (Term.structInst
           "{"
           []
           [(group
             (Term.structInstField
              (Term.structInstLVal `toFun [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [`e] [])] "=>" (Term.proj `e "." `val))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `invFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [`e] [])]
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [`e
                  ","
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(group (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `hα)] "]") []) [])
                      (group (Tactic.exact "exact" `IntermediateField.mem_top) [])])))]
                 "⟩"))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `left_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [(Term.simpleBinder [(Term.hole "_")] [])]
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                    (group (Tactic.tacticRfl "rfl") [])]))))))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `right_inv [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl)))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `map_mul' [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `map_add' [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_") (Term.hole "_")] [])] "=>" `rfl)))
             [","])
            (group
             (Term.structInstField
              (Term.structInstLVal `commutes' [])
              ":="
              (Term.fun "fun" (Term.basicFun [(Term.simpleBinder [(Term.hole "_")] [])] "=>" `rfl)))
             [])]
           (Term.optEllipsis [])
           []
           "}"))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`H []]
          [(Term.typeSpec ":" (Term.app `IsIntegral [`F `α]))]
          ":="
          (Term.app `IsGalois.integral [`F `α]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_sep []]
          [(Term.typeSpec ":" (Term.proj (Term.app `minpoly [`F `α]) "." `Separable))]
          ":="
          (Term.app `IsGalois.separable [`F `α]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h_splits []]
          [(Term.typeSpec
            ":"
            (Term.app (Term.proj (Term.app `minpoly [`F `α]) "." `Splits) [(Term.app `algebraMap [`F `E])]))]
          ":="
          (Term.app `IsGalois.splits [`F `α]))))
       [])
      (group
       (Tactic.replace'
        "replace"
        [`h_splits []]
        [(Term.typeSpec
          ":"
          (Term.app
           `Polynomial.Splits
           [(Term.app
             `algebraMap
             [`F
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯")])
            (Term.app `minpoly [`F `α])]))])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.tacticHave_
           "have"
           (Term.haveDecl
            (Term.haveIdDecl
             [`p []]
             [(Term.typeSpec
               ":"
               («term_=_»
                (Term.app `iso.symm.to_alg_hom.to_ring_hom.comp [(Term.app `algebraMap [`F `E])])
                "="
                (Term.app
                 `algebraMap
                 [`F
                  (Init.Coe.«term↥_»
                   "↥"
                   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                    `F
                    "⟮"
                    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                    "⟯"))])))]
             ":="
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
                 (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
          [])
         (group
          (Mathlib.Tactic.tacticSimpa!?_
           "simpa"
           []
           []
           (Mathlib.Tactic.simpaArgsRest
            []
            []
            []
            [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `p)] "]")]
            []
            [(Tactic.usingArg
              "using"
              (Term.app
               `Polynomial.splits_comp_of_splits
               [(Term.app `algebraMap [`F `E]) `iso.symm.to_alg_hom.to_ring_hom `h_splits]))]))
          [])])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `LinearEquiv.finrank_eq [`iso.to_linear_equiv]))] "]")
        [])
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app `intermediate_field.adjoin_simple.card_aut_eq_finrank [`F `E `H `h_sep `h_splits]))]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" `Fintype.card_congr) [])
      (group
       (Tactic.apply
        "apply"
        (Term.app
         `Equivₓ.mk
         [(Term.fun
           "fun"
           (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])))
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`ϕ] [])]
            "=>"
            (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])))]))
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.intro "intro" [`ϕ]) [])
         (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
         (group
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `apply_symm_apply)] "]"]
           [])
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group (Tactic.intro "intro" [`ϕ]) [])
         (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
         (group
          (Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `symm_apply_apply)] "]"]
           [])
          [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group (Tactic.intro "intro" [`ϕ]) [])
    (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
    (group
     (Tactic.simp
      "simp"
      []
      []
      ["only"]
      ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `symm_apply_apply)] "]"]
      [])
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `symm_apply_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `symm_apply_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `trans_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`ϕ])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group (Tactic.intro "intro" [`ϕ]) [])
    (group (Mathlib.Tactic.Ext.tacticExt1___ "ext1" []) [])
    (group
     (Tactic.simp
      "simp"
      []
      []
      ["only"]
      ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `apply_symm_apply)] "]"]
      [])
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp
   "simp"
   []
   []
   ["only"]
   ["[" [(Tactic.simpLemma [] [] `trans_apply) "," (Tactic.simpLemma [] [] `apply_symm_apply)] "]"]
   [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `apply_symm_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `trans_apply
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Ext.tacticExt1___ "ext1" [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`ϕ])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    `Equivₓ.mk
    [(Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])))
     (Term.fun
      "fun"
      (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Equivₓ.mk
   [(Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])))
    (Term.fun
     "fun"
     (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `iso.symm.trans [(Term.app `trans [`ϕ `iso])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `trans [`ϕ `iso])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iso
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `trans [`ϕ `iso]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `iso.symm.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.fun
   "fun"
   (Term.basicFun [(Term.simpleBinder [`ϕ] [])] "=>" (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `iso.trans [(Term.app `trans [`ϕ `iso.symm])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `trans [`ϕ `iso.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iso.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `ϕ
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `trans [`ϕ `iso.symm]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `iso.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`ϕ] [])]
    "=>"
    (Term.app `iso.trans [(Term.paren "(" [(Term.app `trans [`ϕ `iso.symm]) []] ")")])))
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Equivₓ.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `Fintype.card_congr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule ["←"] (Term.app `intermediate_field.adjoin_simple.card_aut_eq_finrank [`F `E `H `h_sep `h_splits]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `intermediate_field.adjoin_simple.card_aut_eq_finrank [`F `E `H `h_sep `h_splits])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_splits
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `h_sep
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `intermediate_field.adjoin_simple.card_aut_eq_finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq "[" [(Tactic.rwRule ["←"] (Term.app `LinearEquiv.finrank_eq [`iso.to_linear_equiv]))] "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `LinearEquiv.finrank_eq [`iso.to_linear_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `iso.to_linear_equiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `LinearEquiv.finrank_eq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.tacticHave_
      "have"
      (Term.haveDecl
       (Term.haveIdDecl
        [`p []]
        [(Term.typeSpec
          ":"
          («term_=_»
           (Term.app `iso.symm.to_alg_hom.to_ring_hom.comp [(Term.app `algebraMap [`F `E])])
           "="
           (Term.app
            `algebraMap
            [`F
             (Init.Coe.«term↥_»
              "↥"
              (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
               `F
               "⟮"
               (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
               "⟯"))])))]
        ":="
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
            (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
     [])
    (group
     (Mathlib.Tactic.tacticSimpa!?_
      "simpa"
      []
      []
      (Mathlib.Tactic.simpaArgsRest
       []
       []
       []
       [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `p)] "]")]
       []
       [(Tactic.usingArg
         "using"
         (Term.app
          `Polynomial.splits_comp_of_splits
          [(Term.app `algebraMap [`F `E]) `iso.symm.to_alg_hom.to_ring_hom `h_splits]))]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Mathlib.Tactic.tacticSimpa!?_
   "simpa"
   []
   []
   (Mathlib.Tactic.simpaArgsRest
    []
    []
    []
    [(Tactic.simpArgs "[" [(Tactic.simpLemma [] [] `p)] "]")]
    []
    [(Tactic.usingArg
      "using"
      (Term.app
       `Polynomial.splits_comp_of_splits
       [(Term.app `algebraMap [`F `E]) `iso.symm.to_alg_hom.to_ring_hom `h_splits]))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Polynomial.splits_comp_of_splits
   [(Term.app `algebraMap [`F `E]) `iso.symm.to_alg_hom.to_ring_hom `h_splits])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h_splits
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `iso.symm.to_alg_hom.to_ring_hom
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `algebraMap [`F `E])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `algebraMap [`F `E]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.splits_comp_of_splits
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `p
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.tacticHave_
   "have"
   (Term.haveDecl
    (Term.haveIdDecl
     [`p []]
     [(Term.typeSpec
       ":"
       («term_=_»
        (Term.app `iso.symm.to_alg_hom.to_ring_hom.comp [(Term.app `algebraMap [`F `E])])
        "="
        (Term.app
         `algebraMap
         [`F
          (Init.Coe.«term↥_»
           "↥"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `F
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯"))])))]
     ":="
     (Term.byTactic
      "by"
      (Tactic.tacticSeq
       (Tactic.tacticSeq1Indented
        [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) [])
         (group (Tactic.simp "simp" [] [] [] [] []) [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] []) []) (group (Tactic.simp "simp" [] [] [] [] []) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.simp "simp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Mathlib.Tactic.Ext.«tacticExt___:_» "ext" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («term_=_»
   (Term.app `iso.symm.to_alg_hom.to_ring_hom.comp [(Term.app `algebraMap [`F `E])])
   "="
   (Term.app
    `algebraMap
    [`F
     (Init.Coe.«term↥_»
      "↥"
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `F
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `algebraMap
   [`F
    (Init.Coe.«term↥_»
     "↥"
     (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
      `F
      "⟮"
      (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
      "⟯"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Init.Coe.«term↥_»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Init.Coe.«term↥_»
   "↥"
   (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
    `F
    "⟮"
    (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
    "⟯"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `F
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  card_aut_eq_finrank
  [ FiniteDimensional F E ] [ IsGalois F E ] : Fintype.card E ≃ₐ[ F ] E = finrank F E
  :=
    by
      cases' Field.exists_primitive_element F E with α hα
        let
          iso
            : F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ ≃ₐ[ F ] E
            :=
            {
              toFun := fun e => e . val ,
                invFun := fun e => ⟨ e , by rw [ hα ] exact IntermediateField.mem_top ⟩ ,
                left_inv := fun _ => by ext rfl ,
                right_inv := fun _ => rfl ,
                map_mul' := fun _ _ => rfl ,
                map_add' := fun _ _ => rfl ,
                commutes' := fun _ => rfl
              }
        have H : IsIntegral F α := IsGalois.integral F α
        have h_sep : minpoly F α . Separable := IsGalois.separable F α
        have h_splits : minpoly F α . Splits algebraMap F E := IsGalois.splits F α
        replace
          h_splits
          :
            Polynomial.Splits
              algebraMap F F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯ minpoly F α
        ·
          have
              p
                :
                  iso.symm.to_alg_hom.to_ring_hom.comp algebraMap F E
                    =
                    algebraMap F ↥ F ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                :=
                by ext simp
            simpa [ p ] using Polynomial.splits_comp_of_splits algebraMap F E iso.symm.to_alg_hom.to_ring_hom h_splits
        rw [ ← LinearEquiv.finrank_eq iso.to_linear_equiv ]
        rw [ ← intermediate_field.adjoin_simple.card_aut_eq_finrank F E H h_sep h_splits ]
        apply Fintype.card_congr
        apply Equivₓ.mk fun ϕ => iso.trans trans ϕ iso.symm fun ϕ => iso.symm.trans trans ϕ iso
        · intro ϕ ext1 simp only [ trans_apply , apply_symm_apply ]
        · intro ϕ ext1 simp only [ trans_apply , symm_apply_apply ]

end IsGalois

end

section IsGaloisTower

variable (F K E : Type _) [Field F] [Field K] [Field E] {E' : Type _} [Field E'] [Algebra F E']

variable [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

theorem IsGalois.tower_top_of_is_galois [IsGalois F E] : IsGalois K E :=
  { to_is_separable := is_separable_tower_top_of_is_separable F K E, to_normal := Normal.tower_top_of_normal F K E }

variable {F E}

-- see Note [lower instance priority]
instance (priority := 100) IsGalois.tower_top_intermediate_field (K : IntermediateField F E) [h : IsGalois F E] :
    IsGalois K E :=
  IsGalois.tower_top_of_is_galois F K E

theorem is_galois_iff_is_galois_bot : IsGalois (⊥ : IntermediateField F E) E ↔ IsGalois F E := by
  constructor
  · intro h
    exact IsGalois.tower_top_of_is_galois (⊥ : IntermediateField F E) F E
    
  · intro h
    infer_instance
    

theorem IsGalois.of_alg_equiv [h : IsGalois F E] (f : E ≃ₐ[F] E') : IsGalois F E' :=
  { to_is_separable := IsSeparable.of_alg_hom F E f.symm, to_normal := Normal.of_alg_equiv f }

theorem AlgEquiv.transfer_galois (f : E ≃ₐ[F] E') : IsGalois F E ↔ IsGalois F E' :=
  ⟨fun h => IsGalois.of_alg_equiv f, fun h => IsGalois.of_alg_equiv f.symm⟩

theorem is_galois_iff_is_galois_top : IsGalois F (⊤ : IntermediateField F E) ↔ IsGalois F E :=
  (IntermediateField.topEquiv : (⊤ : IntermediateField F E) ≃ₐ[F] E).transfer_galois

instance is_galois_bot : IsGalois F (⊥ : IntermediateField F E) :=
  (IntermediateField.botEquiv F E).transfer_galois.mpr (IsGalois.self F)

end IsGaloisTower

section GaloisCorrespondence

variable {F : Type _} [Field F] {E : Type _} [Field E] [Algebra F E]

variable (H : Subgroup (E ≃ₐ[F] E)) (K : IntermediateField F E)

/-- The intermediate field of fixed points fixed by a monoid action that commutes with the
`F`-action on `E`. -/
def FixedPoints.intermediateField (M : Type _) [Monoidₓ M] [MulSemiringAction M E] [SmulCommClass M F E] :
    IntermediateField F E :=
  { FixedPoints.subfield M E with Carrier := MulAction.FixedPoints M E,
    algebra_map_mem' := fun a g => by
      rw [Algebra.algebra_map_eq_smul_one, smul_comm, smul_one] }

namespace IntermediateField

/-- The intermediate_field fixed by a subgroup -/
def fixedField : IntermediateField F E :=
  FixedPoints.intermediateField H

theorem finrank_fixed_field_eq_card [FiniteDimensional F E] [DecidablePred (· ∈ H)] :
    finrank (fixedField H) E = Fintype.card H :=
  FixedPoints.finrank_eq_card H E

/-- The subgroup fixing an intermediate_field -/
def fixingSubgroup : Subgroup (E ≃ₐ[F] E) :=
  fixingSubgroup (E ≃ₐ[F] E) (K : Set E)

theorem le_iff_le : K ≤ fixedField H ↔ H ≤ fixingSubgroup K :=
  ⟨fun h g hg x => h (Subtype.mem x) ⟨g, hg⟩, fun h x hx g => h (Subtype.mem g) ⟨x, hx⟩⟩

/-- The fixing_subgroup of `K : intermediate_field F E` is isomorphic to `E ≃ₐ[K] E` -/
def fixingSubgroupEquiv : fixingSubgroup K ≃* E ≃ₐ[K] E where
  toFun := fun ϕ => { AlgEquiv.toRingEquiv ↑ϕ with commutes' := ϕ.Mem }
  invFun := fun ϕ => ⟨ϕ.restrictScalars _, ϕ.commutes⟩
  left_inv := fun _ => by
    ext
    rfl
  right_inv := fun _ => by
    ext
    rfl
  map_mul' := fun _ _ => by
    ext
    rfl

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem fixing_subgroup_fixed_field [FiniteDimensional F E] : fixingSubgroup (fixedField H) = H := by
  have H_le : H ≤ fixingSubgroup (fixed_field H) := (le_iff_le _ _).mp le_rfl
  classical
  suffices Fintype.card H = Fintype.card (fixingSubgroup (fixed_field H)) by
    exact
      SetLike.coe_injective
        (Set.eq_of_inclusion_surjective
            ((Fintype.bijective_iff_injective_and_card (Set.inclusion H_le)).mpr
                ⟨Set.inclusion_injective H_le, this⟩).2).symm
  apply Fintype.card_congr
  refine' (FixedPoints.toAlgHomEquiv H E).trans _
  refine' (algEquivEquivAlgHom (fixed_field H) E).symm.trans _
  exact (fixing_subgroup_equiv (fixed_field H)).toEquiv.symm

instance fixedField.algebra : Algebra K (fixedField (fixingSubgroup K)) where
  smul := fun x y =>
    ⟨x * y, fun ϕ => by
      rw [smul_mul', show ϕ • ↑x = ↑x from Subtype.mem ϕ x, show ϕ • ↑y = ↑y from Subtype.mem y ϕ]⟩
  toFun := fun x => ⟨x, fun ϕ => Subtype.mem ϕ x⟩
  map_zero' := rfl
  map_add' := fun _ _ => rfl
  map_one' := rfl
  map_mul' := fun _ _ => rfl
  commutes' := fun _ _ => mul_comm _ _
  smul_def' := fun _ _ => rfl

instance fixedField.is_scalar_tower : IsScalarTower K (fixedField (fixingSubgroup K)) E :=
  ⟨fun _ _ _ => mul_assoc _ _ _⟩

end IntermediateField

namespace IsGalois

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem fixed_field_fixing_subgroup [FiniteDimensional F E] [h : IsGalois F E] :
    IntermediateField.fixedField (IntermediateField.fixingSubgroup K) = K := by
  have K_le : K ≤ IntermediateField.fixedField (IntermediateField.fixingSubgroup K) :=
    (IntermediateField.le_iff_le _ _).mpr le_rfl
  suffices finrank K E = finrank (IntermediateField.fixedField (IntermediateField.fixingSubgroup K)) E by
    exact (IntermediateField.eq_of_le_of_finrank_eq' K_le this).symm
  classical
  rw [IntermediateField.finrank_fixed_field_eq_card,
    Fintype.card_congr (IntermediateField.fixingSubgroupEquiv K).toEquiv]
  exact (card_aut_eq_finrank K E).symm

theorem card_fixing_subgroup_eq_finrank [DecidablePred (· ∈ IntermediateField.fixingSubgroup K)] [FiniteDimensional F E]
    [IsGalois F E] : Fintype.card (IntermediateField.fixingSubgroup K) = finrank K E := by
  conv => rhs rw [← fixed_field_fixing_subgroup K, IntermediateField.finrank_fixed_field_eq_card]

/-- The Galois correspondence from intermediate fields to subgroups -/
def intermediateFieldEquivSubgroup [FiniteDimensional F E] [IsGalois F E] :
    IntermediateField F E ≃o (Subgroup (E ≃ₐ[F] E))ᵒᵈ where
  toFun := IntermediateField.fixingSubgroup
  invFun := IntermediateField.fixedField
  left_inv := fun K => fixed_field_fixing_subgroup K
  right_inv := fun H => IntermediateField.fixing_subgroup_fixed_field H
  map_rel_iff' := fun K L => by
    rw [← fixed_field_fixing_subgroup L, IntermediateField.le_iff_le, fixed_field_fixing_subgroup L, ←
      OrderDual.dual_le]
    rfl

/-- The Galois correspondence as a galois_insertion -/
def galoisInsertionIntermediateFieldSubgroup [FiniteDimensional F E] :
    GaloisInsertion
      (OrderDual.toDual ∘ (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘ OrderDual.toDual) where
  choice := fun K _ => IntermediateField.fixingSubgroup K
  gc := fun K H => (IntermediateField.le_iff_le H K).symm
  le_l_u := fun H => le_of_eqₓ (IntermediateField.fixing_subgroup_fixed_field H).symm
  choice_eq := fun K _ => rfl

/-- The Galois correspondence as a galois_coinsertion -/
def galoisCoinsertionIntermediateFieldSubgroup [FiniteDimensional F E] [IsGalois F E] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (IntermediateField.fixingSubgroup : IntermediateField F E → Subgroup (E ≃ₐ[F] E)))
      ((IntermediateField.fixedField : Subgroup (E ≃ₐ[F] E) → IntermediateField F E) ∘ OrderDual.toDual) where
  choice := fun H _ => IntermediateField.fixedField H
  gc := fun K H => (IntermediateField.le_iff_le H K).symm
  u_l_le := fun K => le_of_eqₓ (fixed_field_fixing_subgroup K)
  choice_eq := fun H _ => rfl

end IsGalois

end GaloisCorrespondence

section GaloisEquivalentDefinitions

variable (F : Type _) [Field F] (E : Type _) [Field E] [Algebra F E]

namespace IsGalois

theorem is_separable_splitting_field [FiniteDimensional F E] [IsGalois F E] :
    ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E := by
  cases' Field.exists_primitive_element F E with α h1
  use minpoly F α, separable F α, IsGalois.splits F α
  rw [eq_top_iff, ← IntermediateField.top_to_subalgebra, ← h1]
  rw [IntermediateField.adjoin_simple_to_subalgebra_of_integral F α (integral F α)]
  apply Algebra.adjoin_mono
  rw [Set.singleton_subset_iff, Finset.mem_coe, Multiset.mem_to_finset, Polynomial.mem_roots]
  · dsimp' only [Polynomial.IsRoot]
    rw [Polynomial.eval_map, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
    
  · exact Polynomial.map_ne_zero (minpoly.ne_zero (integral F α))
    

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem of_fixed_field_eq_bot [FiniteDimensional F E]
    (h : IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥) : IsGalois F E := by
  rw [← is_galois_iff_is_galois_bot, ← h]
  classical
  exact IsGalois.of_fixed_field E (⊤ : Subgroup (E ≃ₐ[F] E))

-- ././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: classical ... #[[]]
theorem of_card_aut_eq_finrank [FiniteDimensional F E] (h : Fintype.card (E ≃ₐ[F] E) = finrank F E) : IsGalois F E := by
  apply of_fixed_field_eq_bot
  have p : 0 < finrank (IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E))) E := finrank_pos
  classical
  rw [← IntermediateField.finrank_eq_one_iff, ← mul_left_inj' (ne_of_ltₓ p).symm, finrank_mul_finrank, ← h, one_mulₓ,
    IntermediateField.finrank_fixed_field_eq_card]
  apply Fintype.card_congr
  exact
    { toFun := fun g => ⟨g, Subgroup.mem_top g⟩, invFun := coe, left_inv := fun g => rfl,
      right_inv := fun _ => by
        ext
        rfl }

variable {F} {E} {p : F[X]}

-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
-- ././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)
/- failed to parenthesize: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
[PrettyPrinter.parenthesize.input] (Command.declaration
 (Command.declModifiers [] [] [] [] [] [])
 (Command.theorem
  "theorem"
  (Command.declId `of_separable_splitting_field_aux [])
  (Command.declSig
   [(Term.instBinder "[" [`hFE ":"] (Term.app `FiniteDimensional [`F `E]) "]")
    (Term.instBinder "[" [`sp ":"] (Term.app (Term.proj `p "." `IsSplittingField) [`F `E]) "]")
    (Term.explicitBinder "(" [`hp] [":" (Term.proj `p "." `Separable)] [] ")")
    (Term.explicitBinder "(" [`K] [":" (Term.app `IntermediateField [`F `E])] [] ")")
    (Term.implicitBinder "{" [`x] [":" `E] "}")
    (Term.explicitBinder
     "("
     [`hx]
     [":" («term_∈_» `x "∈" (Term.proj (Term.app (Term.proj `p "." `map) [(Term.app `algebraMap [`F `E])]) "." `roots))]
     []
     ")")]
   (Term.typeSpec
    ":"
    («term_=_»
     (Term.app
      `Fintype.card
      [(Algebra.Algebra.Basic.«term_→ₐ[_]_»
        (Term.paren
         "("
         [(coeNotation
           "↑"
           (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
            `K
            "⟮"
            (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
            "⟯"))
          [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
         ")")
        " →ₐ["
        `F
        "] "
        `E)])
     "="
     («term_*_»
      (Term.app `Fintype.card [(Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E)])
      "*"
      (Term.app
       `finrank
       [`K
        (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
         `K
         "⟮"
         (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
         "⟯")])))))
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
           [`h []]
           [(Term.typeSpec ":" (Term.app `IsIntegral [`K `x]))]
           ":="
           (Term.app
            `is_integral_of_is_scalar_tower
            [`x
             (Term.app
              `is_integral_of_noetherian
              [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`hFE]) `x])]))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h1 []]
           [(Term.typeSpec ":" («term_≠_» `p "≠" (num "0")))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`hp] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (tacticRwa__
                   "rwa"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `hp)
                     ","
                     (Tactic.rwRule [] `Polynomial.map_zero)
                     ","
                     (Tactic.rwRule [] `Polynomial.roots_zero)]
                    "]")
                   [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                  [])]))))))))
        [])
       (group
        (Tactic.tacticHave_
         "have"
         (Term.haveDecl
          (Term.haveIdDecl
           [`h2 []]
           [(Term.typeSpec
             ":"
             («term_∣_» (Term.app `minpoly [`K `x]) "∣" (Term.app `p.map [(Term.app `algebraMap [`F `K])])))]
           ":="
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(group (Tactic.apply "apply" `minpoly.dvd) [])
               (group
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Polynomial.aeval_def)
                   ","
                   (Tactic.rwRule [] `Polynomial.eval₂_map)
                   ","
                   (Tactic.rwRule ["←"] `Polynomial.eval_map)]
                  "]")
                 [])
                [])
               (group
                (Tactic.exact
                 "exact"
                 (Term.app
                  (Term.proj (Term.app `Polynomial.mem_roots [(Term.app `Polynomial.map_ne_zero [`h1])]) "." `mp)
                  [`hx]))
                [])]))))))
        [])
       (group
        (Tactic.tacticLet_
         "let"
         (Term.letDecl
          (Term.letIdDecl
           `key_equiv
           []
           [(Term.typeSpec
             ":"
             (Logic.Equiv.Basic.«term_≃_»
              (Algebra.Algebra.Basic.«term_→ₐ[_]_»
               (Term.paren
                "("
                [(coeNotation
                  "↑"
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `K
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯"))
                 [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
                ")")
               " →ₐ["
               `F
               "] "
               `E)
              " ≃ "
              («termΣ_,_»
               "Σ"
               (Lean.explicitBinders
                (Lean.unbracketedExplicitBinders
                 [(Lean.binderIdent `f)]
                 [":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E)]))
               ","
               (Term.app
                (Term.explicit "@" `AlgHom)
                [`K
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `K
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `E
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app `RingHom.toAlgebra [`f])]))))]
           ":="
           (Term.app
            `Equivₓ.trans
            [(Term.app
              `AlgEquiv.arrowCongr
              [(Term.app
                `IntermediateField.lift2AlgEquiv
                [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `K
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")])
               `AlgEquiv.refl])
             `algHomEquivSigma]))))
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
              [(Term.simpleBinder
                [`f]
                [(Term.typeSpec ":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E))])]
              ","
              (Term.app
               `Fintype
               [(Term.app
                 (Term.explicit "@" `AlgHom)
                 [`K
                  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                   `K
                   "⟮"
                   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                   "⟯")
                  `E
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.hole "_")
                  (Term.app `RingHom.toAlgebra [`f])])])))]
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [(Term.simpleBinder [`f] [])]
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(group
                  (Tactic.apply
                   "apply"
                   (Term.app
                    `Fintype.ofInjective
                    [(Term.app `Sigma.mk [`f])
                     (Term.fun
                      "fun"
                      (Term.basicFun
                       [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
                       "=>"
                       (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
                  [])
                 (group (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])) [])]))))))))
        [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule [] (Term.app `Fintype.card_congr [`key_equiv]))
           ","
           (Tactic.rwRule [] `Fintype.card_sigma)
           ","
           (Tactic.rwRule [] (Term.app `IntermediateField.adjoin.finrank [`h]))]
          "]")
         [])
        [])
       (group (Tactic.apply "apply" `Finset.sum_const_nat) [])
       (group (Tactic.intro "intro" [`f `hf]) [])
       (group
        (Tactic.rwSeq
         "rw"
         []
         (Tactic.rwRuleSeq
          "["
          [(Tactic.rwRule
            ["←"]
            (Term.app
             (Term.explicit "@" `IntermediateField.card_alg_hom_adjoin_integral)
             [`K
              (Term.hole "_")
              `E
              (Term.hole "_")
              (Term.hole "_")
              `x
              `E
              (Term.hole "_")
              (Term.app `RingHom.toAlgebra [`f])
              `h]))]
          "]")
         [])
        [])
       (group
        («tactic·.__;_» "·" [(group (Tactic.apply "apply" `Fintype.card_congr) []) (group (Tactic.tacticRfl "rfl") [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.exact
            "exact"
            (Term.app
             `Polynomial.Separable.of_dvd
             [(Term.app
               (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr)
               [`hp])
              `h2]))
           [])])
        [])
       (group
        («tactic·.__;_»
         "·"
         [(group
           (Tactic.refine'
            "refine'"
            (Term.app
             `Polynomial.splits_of_splits_of_dvd
             [(Term.hole "_") (Term.app `Polynomial.map_ne_zero [`h1]) (Term.hole "_") `h2]))
           [])
          (group
           (Tactic.rwSeq
            "rw"
            []
            (Tactic.rwRuleSeq
             "["
             [(Tactic.rwRule [] `Polynomial.splits_map_iff) "," (Tactic.rwRule ["←"] `IsScalarTower.algebra_map_eq)]
             "]")
            [])
           [])
          (group (Tactic.exact "exact" `sp.splits) [])])
        [])])))
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
     [(group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h []]
          [(Term.typeSpec ":" (Term.app `IsIntegral [`K `x]))]
          ":="
          (Term.app
           `is_integral_of_is_scalar_tower
           [`x
            (Term.app
             `is_integral_of_noetherian
             [(Term.app (Term.proj `IsNoetherian.iff_fg "." (fieldIdx "2")) [`hFE]) `x])]))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h1 []]
          [(Term.typeSpec ":" («term_≠_» `p "≠" (num "0")))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`hp] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (tacticRwa__
                  "rwa"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `hp)
                    ","
                    (Tactic.rwRule [] `Polynomial.map_zero)
                    ","
                    (Tactic.rwRule [] `Polynomial.roots_zero)]
                   "]")
                  [(Tactic.location "at" (Tactic.locationHyp [`hx] []))])
                 [])]))))))))
       [])
      (group
       (Tactic.tacticHave_
        "have"
        (Term.haveDecl
         (Term.haveIdDecl
          [`h2 []]
          [(Term.typeSpec
            ":"
            («term_∣_» (Term.app `minpoly [`K `x]) "∣" (Term.app `p.map [(Term.app `algebraMap [`F `K])])))]
          ":="
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(group (Tactic.apply "apply" `minpoly.dvd) [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] `Polynomial.aeval_def)
                  ","
                  (Tactic.rwRule [] `Polynomial.eval₂_map)
                  ","
                  (Tactic.rwRule ["←"] `Polynomial.eval_map)]
                 "]")
                [])
               [])
              (group
               (Tactic.exact
                "exact"
                (Term.app
                 (Term.proj (Term.app `Polynomial.mem_roots [(Term.app `Polynomial.map_ne_zero [`h1])]) "." `mp)
                 [`hx]))
               [])]))))))
       [])
      (group
       (Tactic.tacticLet_
        "let"
        (Term.letDecl
         (Term.letIdDecl
          `key_equiv
          []
          [(Term.typeSpec
            ":"
            (Logic.Equiv.Basic.«term_≃_»
             (Algebra.Algebra.Basic.«term_→ₐ[_]_»
              (Term.paren
               "("
               [(coeNotation
                 "↑"
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `K
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯"))
                [(Term.typeAscription ":" (Term.app `IntermediateField [`F `E]))]]
               ")")
              " →ₐ["
              `F
              "] "
              `E)
             " ≃ "
             («termΣ_,_»
              "Σ"
              (Lean.explicitBinders
               (Lean.unbracketedExplicitBinders
                [(Lean.binderIdent `f)]
                [":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E)]))
              ","
              (Term.app
               (Term.explicit "@" `AlgHom)
               [`K
                (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `K
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")
                `E
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.hole "_")
                (Term.app `RingHom.toAlgebra [`f])]))))]
          ":="
          (Term.app
           `Equivₓ.trans
           [(Term.app
             `AlgEquiv.arrowCongr
             [(Term.app
               `IntermediateField.lift2AlgEquiv
               [(IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                 `K
                 "⟮"
                 (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                 "⟯")])
              `AlgEquiv.refl])
            `algHomEquivSigma]))))
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
             [(Term.simpleBinder [`f] [(Term.typeSpec ":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E))])]
             ","
             (Term.app
              `Fintype
              [(Term.app
                (Term.explicit "@" `AlgHom)
                [`K
                 (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
                  `K
                  "⟮"
                  (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
                  "⟯")
                 `E
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.hole "_")
                 (Term.app `RingHom.toAlgebra [`f])])])))]
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [`f] [])]
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(group
                 (Tactic.apply
                  "apply"
                  (Term.app
                   `Fintype.ofInjective
                   [(Term.app `Sigma.mk [`f])
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
                      "=>"
                      (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
                 [])
                (group (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])) [])]))))))))
       [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule [] (Term.app `Fintype.card_congr [`key_equiv]))
          ","
          (Tactic.rwRule [] `Fintype.card_sigma)
          ","
          (Tactic.rwRule [] (Term.app `IntermediateField.adjoin.finrank [`h]))]
         "]")
        [])
       [])
      (group (Tactic.apply "apply" `Finset.sum_const_nat) [])
      (group (Tactic.intro "intro" [`f `hf]) [])
      (group
       (Tactic.rwSeq
        "rw"
        []
        (Tactic.rwRuleSeq
         "["
         [(Tactic.rwRule
           ["←"]
           (Term.app
            (Term.explicit "@" `IntermediateField.card_alg_hom_adjoin_integral)
            [`K
             (Term.hole "_")
             `E
             (Term.hole "_")
             (Term.hole "_")
             `x
             `E
             (Term.hole "_")
             (Term.app `RingHom.toAlgebra [`f])
             `h]))]
         "]")
        [])
       [])
      (group
       («tactic·.__;_» "·" [(group (Tactic.apply "apply" `Fintype.card_congr) []) (group (Tactic.tacticRfl "rfl") [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.exact
           "exact"
           (Term.app
            `Polynomial.Separable.of_dvd
            [(Term.app (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr) [`hp])
             `h2]))
          [])])
       [])
      (group
       («tactic·.__;_»
        "·"
        [(group
          (Tactic.refine'
           "refine'"
           (Term.app
            `Polynomial.splits_of_splits_of_dvd
            [(Term.hole "_") (Term.app `Polynomial.map_ne_zero [`h1]) (Term.hole "_") `h2]))
          [])
         (group
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Polynomial.splits_map_iff) "," (Tactic.rwRule ["←"] `IsScalarTower.algebra_map_eq)]
            "]")
           [])
          [])
         (group (Tactic.exact "exact" `sp.splits) [])])
       [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.refine'
      "refine'"
      (Term.app
       `Polynomial.splits_of_splits_of_dvd
       [(Term.hole "_") (Term.app `Polynomial.map_ne_zero [`h1]) (Term.hole "_") `h2]))
     [])
    (group
     (Tactic.rwSeq
      "rw"
      []
      (Tactic.rwRuleSeq
       "["
       [(Tactic.rwRule [] `Polynomial.splits_map_iff) "," (Tactic.rwRule ["←"] `IsScalarTower.algebra_map_eq)]
       "]")
      [])
     [])
    (group (Tactic.exact "exact" `sp.splits) [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" `sp.splits)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `sp.splits
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] `Polynomial.splits_map_iff) "," (Tactic.rwRule ["←"] `IsScalarTower.algebra_map_eq)]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IsScalarTower.algebra_map_eq
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Polynomial.splits_map_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.refine'
   "refine'"
   (Term.app
    `Polynomial.splits_of_splits_of_dvd
    [(Term.hole "_") (Term.app `Polynomial.map_ne_zero [`h1]) (Term.hole "_") `h2]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Polynomial.splits_of_splits_of_dvd
   [(Term.hole "_") (Term.app `Polynomial.map_ne_zero [`h1]) (Term.hole "_") `h2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Polynomial.map_ne_zero [`h1])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h1
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.map_ne_zero
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Polynomial.map_ne_zero [`h1]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.splits_of_splits_of_dvd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_»
   "·"
   [(group
     (Tactic.exact
      "exact"
      (Term.app
       `Polynomial.Separable.of_dvd
       [(Term.app (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr) [`hp])
        `h2]))
     [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact
   "exact"
   (Term.app
    `Polynomial.Separable.of_dvd
    [(Term.app (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr) [`hp]) `h2]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Polynomial.Separable.of_dvd
   [(Term.app (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr) [`hp]) `h2])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h2
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr) [`hp])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hp
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.proj (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])]) "." `mpr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Polynomial.separable_map [(Term.app `algebraMap [`F `K])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `algebraMap [`F `K])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `F
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `algebraMap
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `algebraMap [`F `K]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.separable_map
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app `Polynomial.separable_map [(Term.paren "(" [(Term.app `algebraMap [`F `K]) []] ")")]) []]
 ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
 "("
 [(Term.app
   (Term.proj
    (Term.paren
     "("
     [(Term.app `Polynomial.separable_map [(Term.paren "(" [(Term.app `algebraMap [`F `K]) []] ")")]) []]
     ")")
    "."
    `mpr)
   [`hp])
  []]
 ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Polynomial.Separable.of_dvd
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  («tactic·.__;_» "·" [(group (Tactic.apply "apply" `Fintype.card_congr) []) (group (Tactic.tacticRfl "rfl") [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, tactic))
  (Tactic.apply "apply" `Fintype.card_congr)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule
      ["←"]
      (Term.app
       (Term.explicit "@" `IntermediateField.card_alg_hom_adjoin_integral)
       [`K
        (Term.hole "_")
        `E
        (Term.hole "_")
        (Term.hole "_")
        `x
        `E
        (Term.hole "_")
        (Term.app `RingHom.toAlgebra [`f])
        `h]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `IntermediateField.card_alg_hom_adjoin_integral)
   [`K (Term.hole "_") `E (Term.hole "_") (Term.hole "_") `x `E (Term.hole "_") (Term.app `RingHom.toAlgebra [`f]) `h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `RingHom.toAlgebra [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `RingHom.toAlgebra
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `RingHom.toAlgebra [`f]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `x
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `K
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  (Term.explicit "@" `IntermediateField.card_alg_hom_adjoin_integral)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `IntermediateField.card_alg_hom_adjoin_integral
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (some 1024, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.intro "intro" [`f `hf])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `hf
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply "apply" `Finset.sum_const_nat)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Finset.sum_const_nat
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.rwSeq
   "rw"
   []
   (Tactic.rwRuleSeq
    "["
    [(Tactic.rwRule [] (Term.app `Fintype.card_congr [`key_equiv]))
     ","
     (Tactic.rwRule [] `Fintype.card_sigma)
     ","
     (Tactic.rwRule [] (Term.app `IntermediateField.adjoin.finrank [`h]))]
    "]")
   [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `IntermediateField.adjoin.finrank [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `IntermediateField.adjoin.finrank
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `Fintype.card_sigma
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.card_congr [`key_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key_equiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.card_congr
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
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
        [(Term.simpleBinder [`f] [(Term.typeSpec ":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E))])]
        ","
        (Term.app
         `Fintype
         [(Term.app
           (Term.explicit "@" `AlgHom)
           [`K
            (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
             `K
             "⟮"
             (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
             "⟯")
            `E
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.hole "_")
            (Term.app `RingHom.toAlgebra [`f])])])))]
     ":="
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [`f] [])]
       "=>"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(group
            (Tactic.apply
             "apply"
             (Term.app
              `Fintype.ofInjective
              [(Term.app `Sigma.mk [`f])
               (Term.fun
                "fun"
                (Term.basicFun
                 [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
                 "=>"
                 (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
            [])
           (group (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])) [])]))))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [`f] [])]
    "=>"
    (Term.byTactic
     "by"
     (Tactic.tacticSeq
      (Tactic.tacticSeq1Indented
       [(group
         (Tactic.apply
          "apply"
          (Term.app
           `Fintype.ofInjective
           [(Term.app `Sigma.mk [`f])
            (Term.fun
             "fun"
             (Term.basicFun
              [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
              "=>"
              (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
         [])
        (group (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])) [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.byTactic
   "by"
   (Tactic.tacticSeq
    (Tactic.tacticSeq1Indented
     [(group
       (Tactic.apply
        "apply"
        (Term.app
         `Fintype.ofInjective
         [(Term.app `Sigma.mk [`f])
          (Term.fun
           "fun"
           (Term.basicFun
            [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
            "=>"
            (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
       [])
      (group (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])) [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Tactic.exact "exact" (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `Fintype.ofEquiv [(Term.hole "_") `key_equiv])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `key_equiv
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.ofEquiv
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
  (Tactic.apply
   "apply"
   (Term.app
    `Fintype.ofInjective
    [(Term.app `Sigma.mk [`f])
     (Term.fun
      "fun"
      (Term.basicFun
       [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
       "=>"
       (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Fintype.ofInjective
   [(Term.app `Sigma.mk [`f])
    (Term.fun
     "fun"
     (Term.basicFun
      [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
      "=>"
      (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.fun
   "fun"
   (Term.basicFun
    [(Term.simpleBinder [(Term.hole "_") (Term.hole "_") `H] [])]
    "=>"
    (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `eq_of_heq [(Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.proj (Term.app `Sigma.mk.inj [`H]) "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.app `Sigma.mk.inj [`H])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `H
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sigma.mk.inj
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Sigma.mk.inj [`H]) []] ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `eq_of_heq
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.app `Sigma.mk [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Sigma.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Sigma.mk [`f]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `Fintype.ofInjective
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.simpleBinder', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.forall
   "∀"
   [(Term.simpleBinder [`f] [(Term.typeSpec ":" (Algebra.Algebra.Basic.«term_→ₐ[_]_» `K " →ₐ[" `F "] " `E))])]
   ","
   (Term.app
    `Fintype
    [(Term.app
      (Term.explicit "@" `AlgHom)
      [`K
       (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
        `K
        "⟮"
        (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
        "⟯")
       `E
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.hole "_")
       (Term.app `RingHom.toAlgebra [`f])])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   `Fintype
   [(Term.app
     (Term.explicit "@" `AlgHom)
     [`K
      (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
       `K
       "⟮"
       (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
       "⟯")
      `E
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.hole "_")
      (Term.app `RingHom.toAlgebra [`f])])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app
   (Term.explicit "@" `AlgHom)
   [`K
    (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
     `K
     "⟮"
     (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
     "⟯")
    `E
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.hole "_")
    (Term.app `RingHom.toAlgebra [`f])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  (Term.app `RingHom.toAlgebra [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
  `RingHom.toAlgebra
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `RingHom.toAlgebra [`f]) []] ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
  `E
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
  (IntermediateField.FieldTheory.Adjoin.«term_⟮_,⟯»
   `K
   "⟮"
   (str "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\"")
   "⟯")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
  "\"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)\""-/-- failed to format: unknown constant '«"././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)"»'
theorem
  of_separable_splitting_field_aux
  [ hFE : FiniteDimensional F E ]
      [ sp : p . IsSplittingField F E ]
      ( hp : p . Separable )
      ( K : IntermediateField F E )
      { x : E }
      ( hx : x ∈ p . map algebraMap F E . roots )
    :
      Fintype.card
          (
              ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                : IntermediateField F E
              )
            →ₐ[
            F
            ]
            E
        =
        Fintype.card K →ₐ[ F ] E
          *
          finrank K K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
  :=
    by
      have
          h : IsIntegral K x := is_integral_of_is_scalar_tower x is_integral_of_noetherian IsNoetherian.iff_fg . 2 hFE x
        have h1 : p ≠ 0 := fun hp => by rwa [ hp , Polynomial.map_zero , Polynomial.roots_zero ] at hx
        have
          h2
            : minpoly K x ∣ p.map algebraMap F K
            :=
            by
              apply minpoly.dvd
                rw [ Polynomial.aeval_def , Polynomial.eval₂_map , ← Polynomial.eval_map ]
                exact Polynomial.mem_roots Polynomial.map_ne_zero h1 . mp hx
        let
          key_equiv
            :
              (
                    ↑ K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                      : IntermediateField F E
                    )
                  →ₐ[
                  F
                  ]
                  E
                ≃
                Σ
                  f : K →ₐ[ F ] E
                  ,
                  @ AlgHom
                    K
                      K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                      E
                      _
                      _
                      _
                      _
                      RingHom.toAlgebra f
            :=
            Equivₓ.trans
              AlgEquiv.arrowCongr
                  IntermediateField.lift2AlgEquiv
                      K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                    AlgEquiv.refl
                algHomEquivSigma
        have
          :
              ∀
                f : K →ₐ[ F ] E
                ,
                Fintype
                  @ AlgHom
                    K
                      K ⟮ "././Mathport/Syntax/Translate/Basic.lean:812:11: unsupported (impossible)" ⟯
                      E
                      _
                      _
                      _
                      _
                      RingHom.toAlgebra f
            :=
            fun
              f
                =>
                by
                  apply Fintype.ofInjective Sigma.mk f fun _ _ H => eq_of_heq Sigma.mk.inj H . 2
                    exact Fintype.ofEquiv _ key_equiv
        rw [ Fintype.card_congr key_equiv , Fintype.card_sigma , IntermediateField.adjoin.finrank h ]
        apply Finset.sum_const_nat
        intro f hf
        rw [ ← @ IntermediateField.card_alg_hom_adjoin_integral K _ E _ _ x E _ RingHom.toAlgebra f h ]
        · apply Fintype.card_congr rfl
        · exact Polynomial.Separable.of_dvd Polynomial.separable_map algebraMap F K . mpr hp h2
        ·
          refine' Polynomial.splits_of_splits_of_dvd _ Polynomial.map_ne_zero h1 _ h2
            rw [ Polynomial.splits_map_iff , ← IsScalarTower.algebra_map_eq ]
            exact sp.splits

theorem of_separable_splitting_field [sp : p.IsSplittingField F E] (hp : p.Separable) : IsGalois F E := by
  have hFE : FiniteDimensional F E := Polynomial.IsSplittingField.finite_dimensional E p
  let this := Classical.decEq E
  let s := (p.map (algebraMap F E)).roots.toFinset
  have adjoin_root : IntermediateField.adjoin F ↑s = ⊤ := by
    apply IntermediateField.to_subalgebra_injective
    rw [IntermediateField.top_to_subalgebra, ← top_le_iff, ← sp.adjoin_roots]
    apply IntermediateField.algebra_adjoin_le_adjoin
  let P : IntermediateField F E → Prop := fun K => Fintype.card (K →ₐ[F] E) = finrank F K
  suffices P (IntermediateField.adjoin F ↑s) by
    rw [AdjoinRoot] at this
    apply of_card_aut_eq_finrank
    rw [← Eq.trans this (LinearEquiv.finrank_eq intermediate_field.top_equiv.to_linear_equiv)]
    exact
      Fintype.card_congr
        (Equivₓ.trans (algEquivEquivAlgHom F E) (AlgEquiv.arrowCongr intermediate_field.top_equiv.symm AlgEquiv.refl))
  apply IntermediateField.induction_on_adjoin_finset s P
  · have key := IntermediateField.card_alg_hom_adjoin_integral F (show IsIntegral F (0 : E) from is_integral_zero)
    rw [minpoly.zero, Polynomial.nat_degree_X] at key
    specialize key Polynomial.separable_X (Polynomial.splits_X (algebraMap F E))
    rw [← @Subalgebra.finrank_bot F E _ _ _, ← IntermediateField.bot_to_subalgebra] at key
    refine' Eq.trans _ key
    apply Fintype.card_congr
    rw [IntermediateField.adjoin_zero]
    
  intro K x hx hK
  simp only [P] at *
  rw [of_separable_splitting_field_aux hp K (multiset.mem_to_finset.mp hx), hK, finrank_mul_finrank]
  symm
  exact LinearEquiv.finrank_eq (AlgEquiv.toLinearEquiv (IntermediateField.lift2AlgEquiv _))

/-- Equivalent characterizations of a Galois extension of finite degree-/
theorem tfae [FiniteDimensional F E] :
    Tfae
      [IsGalois F E, IntermediateField.fixedField (⊤ : Subgroup (E ≃ₐ[F] E)) = ⊥,
        Fintype.card (E ≃ₐ[F] E) = finrank F E, ∃ p : F[X], p.Separable ∧ p.IsSplittingField F E] :=
  by
  tfae_have 1 → 2
  · exact fun h => OrderIso.map_bot (@intermediate_field_equiv_subgroup F _ E _ _ _ h).symm
    
  tfae_have 1 → 3
  · intro
    exact card_aut_eq_finrank F E
    
  tfae_have 1 → 4
  · intro
    exact is_separable_splitting_field F E
    
  tfae_have 2 → 1
  · exact of_fixed_field_eq_bot F E
    
  tfae_have 3 → 1
  · exact of_card_aut_eq_finrank F E
    
  tfae_have 4 → 1
  · rintro ⟨h, hp1, _⟩
    exact of_separable_splitting_field hp1
    
  tfae_finish

end IsGalois

end GaloisEquivalentDefinitions

