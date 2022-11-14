/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Kevin Buzzard
-/
import Mathbin.Algebra.Homology.Exact
import Mathbin.CategoryTheory.Types
import Mathbin.CategoryTheory.Preadditive.Projective
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Injective objects and categories with enough injectives

An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/


noncomputable section

open CategoryTheory

open CategoryTheory.Limits

open Opposite

universe v v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- An object `J` is injective iff every morphism into `J` can be obtained by extending a monomorphism.
-/
class Injective (J : C) : Prop where
  Factors : ∀ {X Y : C} (g : X ⟶ J) (f : X ⟶ Y) [Mono f], ∃ h : Y ⟶ J, f ≫ h = g
#align category_theory.injective CategoryTheory.Injective

section

/-- An injective presentation of an object `X` consists of a monomorphism `f : X ⟶ J`
to some injective object `J`.
-/
@[nolint has_nonempty_instance]
structure InjectivePresentation (X : C) where
  j : C
  Injective : Injective J := by infer_instance
  f : X ⟶ J
  Mono : Mono f := by infer_instance
#align category_theory.injective_presentation CategoryTheory.InjectivePresentation

variable (C)

/-- A category "has enough injectives" if every object has an injective presentation,
i.e. if for every object `X` there is an injective object `J` and a monomorphism `X ↪ J`. -/
class EnoughInjectives : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)
#align category_theory.enough_injectives CategoryTheory.EnoughInjectives

end

namespace Injective

/-- Let `J` be injective and `g` a morphism into `J`, then `g` can be factored through any monomorphism.
-/
def factorThru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : Y ⟶ J :=
  (Injective.factors g f).some
#align category_theory.injective.factor_thru CategoryTheory.Injective.factorThru

@[simp]
theorem comp_factor_thru {J X Y : C} [Injective J] (g : X ⟶ J) (f : X ⟶ Y) [Mono f] : f ≫ factorThru g f = g :=
  (Injective.factors g f).some_spec
#align category_theory.injective.comp_factor_thru CategoryTheory.Injective.comp_factor_thru

section

open ZeroObject

instance zero_injective [HasZeroObject C] [HasZeroMorphisms C] :
    Injective (0 : C) where Factors X Y g f mono := ⟨0, by ext⟩
#align category_theory.injective.zero_injective CategoryTheory.Injective.zero_injective

end

theorem of_iso {P Q : C} (i : P ≅ Q) (hP : Injective P) : Injective Q :=
  { Factors := fun X Y g f mono => by
      obtain ⟨h, h_eq⟩ := @injective.factors C _ P _ _ _ (g ≫ i.inv) f mono
      refine' ⟨h ≫ i.hom, _⟩
      rw [← category.assoc, h_eq, category.assoc, iso.inv_hom_id, category.comp_id] }
#align category_theory.injective.of_iso CategoryTheory.Injective.of_iso

theorem iso_iff {P Q : C} (i : P ≅ Q) : Injective P ↔ Injective Q :=
  ⟨of_iso i, of_iso i.symm⟩
#align category_theory.injective.iso_iff CategoryTheory.Injective.iso_iff

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The axiom of choice says that every nonempty type is an injective object in `Type`. -/")]
      []
      []
      []
      []
      [])
     (Command.instance
      (Term.attrKind [])
      "instance"
      []
      []
      (Command.declSig
       [(Term.explicitBinder "(" [`X] [":" (Term.type "Type" [`u₁])] [] ")")
        (Term.instBinder "[" [] (Term.app `Nonempty [`X]) "]")]
       (Term.typeSpec ":" (Term.app `Injective [`X])))
      (Command.whereStructInst
       "where"
       [(Command.whereStructField
         (Term.letDecl
          (Term.letIdDecl
           `Factors
           [`Y `Z `g `f `mono]
           []
           ":="
           (Term.anonymousCtor
            "⟨"
            [(Term.fun
              "fun"
              (Term.basicFun
               [`z]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.«tactic_<;>_»
                    (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
                    "<;>"
                    (Tactic.exact
                     "exact"
                     (termDepIfThenElse
                      "if"
                      (Lean.binderIdent `h)
                      ":"
                      («term_∈_» `z "∈" (Term.app `Set.range [`f]))
                      "then"
                      (Term.app `g [(Term.app `Classical.choose [`h])])
                      "else"
                      (Term.app `Nonempty.some [`inferInstance]))))])))))
             ","
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Std.Tactic.Ext.«tacticExt___:_»
                  "ext"
                  [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
                  [])
                 []
                 (Tactic.change
                  "change"
                  («term_=_» (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
                  [])
                 []
                 (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mono_iff_injective)] "]")
                     [(Tactic.location "at" (Tactic.locationHyp [`mono] []))])
                    [])
                   (group
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] (Term.app `mono [(Term.app `Classical.choose_spec [`h])]))]
                      "]")
                     [])
                    [])])
                 []
                 («tactic___;_»
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(group
                    (Tactic.exact
                     "exact"
                     (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])]))
                    [])])])))]
            "⟩"))))]
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
      (Term.anonymousCtor
       "⟨"
       [(Term.fun
         "fun"
         (Term.basicFun
          [`z]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.«tactic_<;>_»
               (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
               "<;>"
               (Tactic.exact
                "exact"
                (termDepIfThenElse
                 "if"
                 (Lean.binderIdent `h)
                 ":"
                 («term_∈_» `z "∈" (Term.app `Set.range [`f]))
                 "then"
                 (Term.app `g [(Term.app `Classical.choose [`h])])
                 "else"
                 (Term.app `Nonempty.some [`inferInstance]))))])))))
        ","
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Std.Tactic.Ext.«tacticExt___:_»
             "ext"
             [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
             [])
            []
            (Tactic.change
             "change"
             («term_=_» (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
             [])
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mono_iff_injective)] "]")
                [(Tactic.location "at" (Tactic.locationHyp [`mono] []))])
               [])
              (group
               (Tactic.rwSeq
                "rw"
                []
                (Tactic.rwRuleSeq
                 "["
                 [(Tactic.rwRule [] (Term.app `mono [(Term.app `Classical.choose_spec [`h])]))]
                 "]")
                [])
               [])])
            []
            («tactic___;_»
             (cdotTk (patternIgnore (token.«·» "·")))
             [(group
               (Tactic.exact
                "exact"
                (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])]))
               [])])])))]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Std.Tactic.Ext.«tacticExt___:_»
           "ext"
           [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
           [])
          []
          (Tactic.change
           "change"
           («term_=_» (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
           [])
          []
          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mono_iff_injective)] "]")
              [(Tactic.location "at" (Tactic.locationHyp [`mono] []))])
             [])
            (group
             (Tactic.rwSeq
              "rw"
              []
              (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mono [(Term.app `Classical.choose_spec [`h])]))] "]")
              [])
             [])])
          []
          («tactic___;_»
           (cdotTk (patternIgnore (token.«·» "·")))
           [(group
             (Tactic.exact "exact" (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])]))
             [])])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.exact "exact" (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])]))
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `False.elim [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `y
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     [(Term.app `h [(Term.anonymousCtor "⟨" [`y "," `rfl] "⟩")]) []]
     ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `False.elim
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («tactic___;_»
       (cdotTk (patternIgnore (token.«·» "·")))
       [(group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mono_iff_injective)] "]")
          [(Tactic.location "at" (Tactic.locationHyp [`mono] []))])
         [])
        (group
         (Tactic.rwSeq
          "rw"
          []
          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mono [(Term.app `Classical.choose_spec [`h])]))] "]")
          [])
         [])])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] (Term.app `mono [(Term.app `Classical.choose_spec [`h])]))] "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `mono [(Term.app `Classical.choose_spec [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.choose_spec [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose_spec
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Classical.choose_spec [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, tactic))
      (Tactic.rwSeq
       "rw"
       []
       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `mono_iff_injective)] "]")
       [(Tactic.location "at" (Tactic.locationHyp [`mono] []))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.locationHyp', expected 'Lean.Parser.Tactic.locationWildcard'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mono
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `mono_iff_injective
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_» (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")]) "=" (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dite
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.Ext.«tacticExt___:_»
       "ext"
       [(Std.Tactic.RCases.rintroPat.one (Std.Tactic.RCases.rcasesPat.one `y))]
       [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`z]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.«tactic_<;>_»
             (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
             "<;>"
             (Tactic.exact
              "exact"
              (termDepIfThenElse
               "if"
               (Lean.binderIdent `h)
               ":"
               («term_∈_» `z "∈" (Term.app `Set.range [`f]))
               "then"
               (Term.app `g [(Term.app `Classical.choose [`h])])
               "else"
               (Term.app `Nonempty.some [`inferInstance]))))])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.«tactic_<;>_»
           (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
           "<;>"
           (Tactic.exact
            "exact"
            (termDepIfThenElse
             "if"
             (Lean.binderIdent `h)
             ":"
             («term_∈_» `z "∈" (Term.app `Set.range [`f]))
             "then"
             (Term.app `g [(Term.app `Classical.choose [`h])])
             "else"
             (Term.app `Nonempty.some [`inferInstance]))))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         («term_∈_» `z "∈" (Term.app `Set.range [`f]))
         "then"
         (Term.app `g [(Term.app `Classical.choose [`h])])
         "else"
         (Term.app `Nonempty.some [`inferInstance]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (termDepIfThenElse
        "if"
        (Lean.binderIdent `h)
        ":"
        («term_∈_» `z "∈" (Term.app `Set.range [`f]))
        "then"
        (Term.app `g [(Term.app `Classical.choose [`h])])
        "else"
        (Term.app `Nonempty.some [`inferInstance])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       («term_∈_» `z "∈" (Term.app `Set.range [`f]))
       "then"
       (Term.app `g [(Term.app `Classical.choose [`h])])
       "else"
       (Term.app `Nonempty.some [`inferInstance]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Nonempty.some [`inferInstance])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `inferInstance
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Nonempty.some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `g [(Term.app `Classical.choose [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Classical.choose [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Classical.choose
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" [(Term.app `Classical.choose [`h]) []] ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_∈_» `z "∈" (Term.app `Set.range [`f]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Set.range [`f])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none, [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Set.range
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none, [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `z
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.basicFun', expected 'Lean.Parser.Term.matchAlts'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letPatDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.letIdDecl', expected 'Lean.Parser.Term.letEqnsDecl'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.instance', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/-- The axiom of choice says that every nonempty type is an injective object in `Type`. -/
  instance
    ( X : Type u₁ ) [ Nonempty X ] : Injective X
    where
      Factors
        Y Z g f mono
        :=
        ⟨
          fun z => by skip <;> exact if h : z ∈ Set.range f then g Classical.choose h else Nonempty.some inferInstance
            ,
            by
              ext y
                change dite _ _ _ = _
                split_ifs
                · rw [ mono_iff_injective ] at mono rw [ mono Classical.choose_spec h ]
                · exact False.elim h ⟨ y , rfl ⟩
          ⟩

instance TypeCat.enough_injectives :
    EnoughInjectives
      (Type
        u₁) where presentation X :=
    Nonempty.intro
      { j := WithBot X, Injective := inferInstance, f := Option.some,
        Mono := by
          rw [mono_iff_injective]
          exact Option.some_injective X }
#align category_theory.injective.Type.enough_injectives CategoryTheory.Injective.TypeCat.enough_injectives

instance {P Q : C} [HasBinaryProduct P Q] [Injective P] [Injective Q] :
    Injective (P ⨯ Q) where Factors X Y g f mono := by
    skip
    use limits.prod.lift (factor_thru (g ≫ limits.prod.fst) f) (factor_thru (g ≫ limits.prod.snd) f)
    simp only [prod.comp_lift, comp_factor_thru]
    ext
    · simp only [prod.lift_fst]
      
    · simp only [prod.lift_snd]
      

instance {β : Type v} (c : β → C) [HasProduct c] [∀ b, Injective (c b)] :
    Injective (∏ c) where Factors X Y g f mono := by
    skip
    refine' ⟨pi.lift fun b => factor_thru (g ≫ pi.π c _) f, _⟩
    ext ⟨j⟩
    simp only [category.assoc, limit.lift_π, fan.mk_π_app, comp_factor_thru]

instance {P Q : C} [HasZeroMorphisms C] [HasBinaryBiproduct P Q] [Injective P] [Injective Q] :
    Injective (P ⊞ Q) where Factors X Y g f mono := by
    skip
    refine' ⟨biprod.lift (factor_thru (g ≫ biprod.fst) f) (factor_thru (g ≫ biprod.snd) f), _⟩
    ext
    · simp only [category.assoc, biprod.lift_fst, comp_factor_thru]
      
    · simp only [category.assoc, biprod.lift_snd, comp_factor_thru]
      

instance {β : Type v} (c : β → C) [HasZeroMorphisms C] [HasBiproduct c] [∀ b, Injective (c b)] :
    Injective (⨁ c) where Factors X Y g f mono := by
    skip
    refine' ⟨biproduct.lift fun b => factor_thru (g ≫ biproduct.π _ _) f, _⟩
    ext
    simp only [category.assoc, biproduct.lift_π, comp_factor_thru]

instance {P : Cᵒᵖ} [Projective P] :
    Injective
      (unop
        P) where Factors X Y g f mono :=
    ⟨(@projective.factor_thru Cᵒᵖ _ P _ _ _ g.op f.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : Cᵒᵖ} [Injective J] :
    Projective
      (unop J) where Factors E X f e he := ⟨(@factor_thru Cᵒᵖ _ J _ _ _ f.op e.op _).unop, Quiver.Hom.op_inj (by simp)⟩

instance {J : C} [Injective J] :
    Projective
      (op J) where Factors E X f e epi := ⟨(@factor_thru C _ J _ _ _ f.unop e.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

instance {P : C} [Projective P] :
    Injective
      (op
        P) where Factors X Y g f mono :=
    ⟨(@projective.factor_thru C _ P _ _ _ g.unop f.unop _).op, Quiver.Hom.unop_inj (by simp)⟩

theorem injective_iff_projective_op {J : C} : Injective J ↔ Projective (op J) :=
  ⟨fun h => inferInstance, fun h => show Injective (unop (op J)) from inferInstance⟩
#align category_theory.injective.injective_iff_projective_op CategoryTheory.Injective.injective_iff_projective_op

theorem projective_iff_injective_op {P : C} : Projective P ↔ Injective (op P) :=
  ⟨fun h => inferInstance, fun h => show Projective (unop (op P)) from inferInstance⟩
#align category_theory.injective.projective_iff_injective_op CategoryTheory.Injective.projective_iff_injective_op

theorem injective_iff_preserves_epimorphisms_yoneda_obj (J : C) : Injective J ↔ (yoneda.obj J).PreservesEpimorphisms :=
  by
  rw [injective_iff_projective_op, projective.projective_iff_preserves_epimorphisms_coyoneda_obj]
  exact functor.preserves_epimorphisms.iso_iff (coyoneda.obj_op_op _)
#align
  category_theory.injective.injective_iff_preserves_epimorphisms_yoneda_obj CategoryTheory.Injective.injective_iff_preserves_epimorphisms_yoneda_obj

section Adjunction

open CategoryTheory.Functor

variable {D : Type u₂} [Category.{v₂} D]

variable {L : C ⥤ D} {R : D ⥤ C} [PreservesMonomorphisms L]

theorem injective_of_adjoint (adj : L ⊣ R) (J : D) [Injective J] : injective <| R.obj J :=
  ⟨fun A A' g f im =>
    ⟨adj.hom_equiv _ _ (factor_thru ((adj.hom_equiv A J).symm g) (L.map f)),
      (adj.hom_equiv _ _).symm.Injective (by simp)⟩⟩
#align category_theory.injective.injective_of_adjoint CategoryTheory.Injective.injective_of_adjoint

end Adjunction

section Preadditive

variable [Preadditive C]

theorem injective_iff_preserves_epimorphisms_preadditive_yoneda_obj (J : C) :
    Injective J ↔ (preadditiveYoneda.obj J).PreservesEpimorphisms := by
  rw [injective_iff_preserves_epimorphisms_yoneda_obj]
  refine' ⟨fun h : (preadditive_yoneda.obj J ⋙ forget _).PreservesEpimorphisms => _, _⟩
  · exact functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_yoneda.obj J) (forget _)
    
  · intro
    exact (inferInstance : (preadditive_yoneda.obj J ⋙ forget _).PreservesEpimorphisms)
    
#align
  category_theory.injective.injective_iff_preserves_epimorphisms_preadditive_yoneda_obj CategoryTheory.Injective.injective_iff_preserves_epimorphisms_preadditive_yoneda_obj

theorem injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' (J : C) :
    Injective J ↔ (preadditiveYonedaObj J).PreservesEpimorphisms := by
  rw [injective_iff_preserves_epimorphisms_yoneda_obj]
  refine' ⟨fun h : (preadditive_yoneda_obj J ⋙ forget _).PreservesEpimorphisms => _, _⟩
  · exact functor.preserves_epimorphisms_of_preserves_of_reflects (preadditive_yoneda_obj J) (forget _)
    
  · intro
    exact (inferInstance : (preadditive_yoneda_obj J ⋙ forget _).PreservesEpimorphisms)
    
#align
  category_theory.injective.injective_iff_preserves_epimorphisms_preadditive_yoneda_obj' CategoryTheory.Injective.injective_iff_preserves_epimorphisms_preadditive_yoneda_obj'

end Preadditive

section EnoughInjectives

variable [EnoughInjectives C]

/-- `injective.under X` provides an arbitrarily chosen injective object equipped with
an monomorphism `injective.ι : X ⟶ injective.under X`.
-/
def under (X : C) : C :=
  (EnoughInjectives.presentation X).some.j
#align category_theory.injective.under CategoryTheory.Injective.under

instance injective_under (X : C) : Injective (under X) :=
  (EnoughInjectives.presentation X).some.Injective
#align category_theory.injective.injective_under CategoryTheory.Injective.injective_under

/-- The monomorphism `injective.ι : X ⟶ injective.under X`
from the arbitrarily chosen injective object under `X`.
-/
def ι (X : C) : X ⟶ under X :=
  (EnoughInjectives.presentation X).some.f
#align category_theory.injective.ι CategoryTheory.Injective.ι

instance ι_mono (X : C) : Mono (ι X) :=
  (EnoughInjectives.presentation X).some.Mono
#align category_theory.injective.ι_mono CategoryTheory.Injective.ι_mono

section

variable [HasZeroMorphisms C] {X Y : C} (f : X ⟶ Y) [HasCokernel f]

/-- When `C` has enough injectives, the object `injective.syzygies f` is
an arbitrarily chosen injective object under `cokernel f`.
-/
def syzygies : C :=
  under (cokernel f)deriving Injective
#align category_theory.injective.syzygies CategoryTheory.Injective.syzygies

/-- When `C` has enough injective,
`injective.d f : Y ⟶ syzygies f` is the composition
`cokernel.π f ≫ ι (cokernel f)`.

(When `C` is abelian, we have `exact f (injective.d f)`.)
-/
abbrev d : Y ⟶ syzygies f :=
  cokernel.π f ≫ ι (cokernel f)
#align category_theory.injective.d CategoryTheory.Injective.d

end

end EnoughInjectives

instance [EnoughInjectives C] : EnoughProjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (unop X)).op, inferInstance⟩⟩⟩

instance [EnoughProjectives C] : EnoughInjectives Cᵒᵖ :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (unop X)).op, inferInstance⟩⟩⟩

theorem enough_projectives_of_enough_injectives_op [EnoughInjectives Cᵒᵖ] : EnoughProjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Injective.ι (op X)).unop, inferInstance⟩⟩⟩
#align
  category_theory.injective.enough_projectives_of_enough_injectives_op CategoryTheory.Injective.enough_projectives_of_enough_injectives_op

theorem enough_injectives_of_enough_projectives_op [EnoughProjectives Cᵒᵖ] : EnoughInjectives C :=
  ⟨fun X => ⟨⟨_, inferInstance, (Projective.π (op X)).unop, inferInstance⟩⟩⟩
#align
  category_theory.injective.enough_injectives_of_enough_projectives_op CategoryTheory.Injective.enough_injectives_of_enough_projectives_op

open Injective

section

variable [HasZeroMorphisms C] [HasImages Cᵒᵖ] [HasEqualizers Cᵒᵖ]

/-- Given a pair of exact morphism `f : Q ⟶ R` and `g : R ⟶ S` and a map `h : R ⟶ J` to an injective
object `J` such that `f ≫ h = 0`, then `g` descents to a map `S ⟶ J`. See below:

```
Q --- f --> R --- g --> S
            |
            | h
            v
            J
```
-/
def Exact.desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S) (hgf : Exact g.op f.op) (w : f ≫ h = 0) :
    S ⟶ J :=
  (Exact.lift h.op g.op f.op hgf (congr_arg Quiver.Hom.op w)).unop
#align category_theory.injective.exact.desc CategoryTheory.Injective.Exact.desc

@[simp]
theorem Exact.comp_desc {J Q R S : C} [Injective J] (h : R ⟶ J) (f : Q ⟶ R) (g : R ⟶ S) (hgf : Exact g.op f.op)
    (w : f ≫ h = 0) : g ≫ Exact.desc h f g hgf w = h := by
  convert congr_arg Quiver.Hom.unop (exact.lift_comp h.op g.op f.op hgf (congr_arg Quiver.Hom.op w))
#align category_theory.injective.exact.comp_desc CategoryTheory.Injective.Exact.comp_desc

end

end Injective

end CategoryTheory

