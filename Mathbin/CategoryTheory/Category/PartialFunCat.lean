/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.CategoryTheory.Category.PointedCat
import Mathbin.Data.Pfun

/-!
# The category of types with partial functions

This defines `PartialFun`, the category of types equipped with partial functions.

This category is classically equivalent to the category of pointed types. The reason it doesn't hold
constructively stems from the difference between `part` and `option`. Both can model partial
functions, but the latter forces a decidable domain.

Precisely, `PartialFun_to_Pointed` turns a partial function `α →. β` into a function
`option α → option β` by sending to `none` the undefined values (and `none` to `none`). But being
defined is (generally) undecidable while being sent to `none` is decidable. So it can't be
constructive.

## References

* [nLab, *The category of sets and partial functions*]
  (https://ncatlab.org/nlab/show/partial+function)
-/


open CategoryTheory Option

universe u

variable {α β : Type _}

/-- The category of types equipped with partial functions. -/
def PartialFunCat : Type _ :=
  Type _
#align PartialFun PartialFunCat

namespace PartialFunCat

instance : CoeSort PartialFunCat (Type _) :=
  ⟨id⟩

/-- Turns a type into a `PartialFun`. -/
@[nolint has_nonempty_instance]
def of : Type _ → PartialFunCat :=
  id
#align PartialFun.of PartialFunCat.of

@[simp]
theorem coe_of (X : Type _) : ↥(of X) = X :=
  rfl
#align PartialFun.coe_of PartialFunCat.coe_of

instance : Inhabited PartialFunCat :=
  ⟨Type _⟩

instance largeCategory :
    LargeCategory.{u} PartialFunCat where 
  Hom := Pfun
  id := Pfun.id
  comp X Y Z f g := g.comp f
  id_comp' := @Pfun.comp_id
  comp_id' := @Pfun.id_comp
  assoc' W X Y Z _ _ _ := (Pfun.comp_assoc _ _ _).symm
#align PartialFun.large_category PartialFunCat.largeCategory

/-- Constructs a partial function isomorphism between types from an equivalence between them. -/
@[simps]
def Iso.mk {α β : PartialFunCat.{u}} (e : α ≃ β) :
    α ≅ β where 
  Hom := e
  inv := e.symm
  hom_inv_id' := (Pfun.coe_comp _ _).symm.trans <| congr_arg coe e.symm_comp_self
  inv_hom_id' := (Pfun.coe_comp _ _).symm.trans <| congr_arg coe e.self_comp_symm
#align PartialFun.iso.mk PartialFunCat.Iso.mk

end PartialFunCat

/-- The forgetful functor from `Type` to `PartialFun` which forgets that the maps are total. -/
def typeToPartialFun : Type u ⥤ PartialFunCat where 
  obj := id
  map := @Pfun.lift
  map_comp' _ _ _ _ _ := Pfun.coe_comp _ _
#align Type_to_PartialFun typeToPartialFun

instance : Faithful typeToPartialFun :=
  ⟨fun X Y => Pfun.coe_injective⟩

/-- The functor which deletes the point of a pointed type. In return, this makes the maps partial.
This the computable part of the equivalence `PartialFun_equiv_Pointed`. -/
@[simps map]
def pointedToPartialFun :
    PointedCat.{u} ⥤ PartialFunCat where 
  obj X := { x : X // x ≠ X.point }
  map X Y f := Pfun.toSubtype _ f.toFun ∘ Subtype.val
  map_id' X :=
    Pfun.ext fun a b => Pfun.mem_to_subtype_iff.trans (Subtype.coe_inj.trans Part.mem_some_iff.symm)
  map_comp' X Y Z f g :=
    Pfun.ext fun a c => by
      refine' (pfun.mem_to_subtype_iff.trans _).trans part.mem_bind_iff.symm
      simp_rw [Pfun.mem_to_subtype_iff, Subtype.exists]
      refine'
        ⟨fun h =>
          ⟨f.to_fun a, fun ha =>
            c.2 <| h.trans ((congr_arg g.to_fun ha : g.to_fun _ = _).trans g.map_point), rfl, h⟩,
          _⟩
      rintro ⟨b, _, rfl : b = _, h⟩
      exact h
#align Pointed_to_PartialFun pointedToPartialFun

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The functor which maps undefined values to a new point. This makes the maps total and creates\npointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't\nbe computable because `= option.none` is decidable while the domain of a general `part` isn't. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance
          (Term.attrKind [])
          (Attr.simps "simps" [] (Attr.simpsArgsRest [] [(group `map)])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `partialFunToPointed [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Functor.Basic.«term_⥤_» `PartialFunCat " ⥤ " `PointedCat))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `obj [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`X]
                  []
                  "=>"
                  (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩"))))
               []
               (Term.structInstField
                (Term.structInstLVal `map [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`X `Y `f]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app
                     `Option.elim'
                     [`none
                      (Term.fun
                       "fun"
                       (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
                    ","
                    `rfl]
                   "⟩"))))
               []
               (Term.structInstField
                (Term.structInstLVal `map_id' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`X]
                  []
                  "=>"
                  («term_<|_»
                   (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                   "<|"
                   (Term.app
                    `funext
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`o]
                       []
                       "=>"
                       (Term.app
                        (Term.app `Option.recOn [`o `rfl])
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.app `Part.some_to_option [(Term.hole "_")])))])))])))))
               []
               (Term.structInstField
                (Term.structInstLVal `map_comp' [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`X `Y `Z `f `g]
                  []
                  "=>"
                  («term_<|_»
                   (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                   "<|"
                   (Term.app
                    `funext
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`o]
                       []
                       "=>"
                       (Term.app
                        (Term.app `Option.recOn [`o `rfl])
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.app
                            `Part.bind_to_option
                            [(Term.hole "_") (Term.hole "_")])))])))])))))]
              (Term.optEllipsis [])
              []
              "}")))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
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
            (Term.structInst
             "{"
             []
             [(Term.structInstField
               (Term.structInstLVal `obj [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`X]
                 []
                 "=>"
                 (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩"))))
              []
              (Term.structInstField
               (Term.structInstLVal `map [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`X `Y `f]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app
                    `Option.elim'
                    [`none
                     (Term.fun
                      "fun"
                      (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
                   ","
                   `rfl]
                  "⟩"))))
              []
              (Term.structInstField
               (Term.structInstLVal `map_id' [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`X]
                 []
                 "=>"
                 («term_<|_»
                  (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                  "<|"
                  (Term.app
                   `funext
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`o]
                      []
                      "=>"
                      (Term.app
                       (Term.app `Option.recOn [`o `rfl])
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.app `Part.some_to_option [(Term.hole "_")])))])))])))))
              []
              (Term.structInstField
               (Term.structInstLVal `map_comp' [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`X `Y `Z `f `g]
                 []
                 "=>"
                 («term_<|_»
                  (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                  "<|"
                  (Term.app
                   `funext
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`o]
                      []
                      "=>"
                      (Term.app
                       (Term.app `Option.recOn [`o `rfl])
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.app
                           `Part.bind_to_option
                           [(Term.hole "_") (Term.hole "_")])))])))])))))]
             (Term.optEllipsis [])
             []
             "}")))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `obj [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`X]
             []
             "=>"
             (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩"))))
          []
          (Term.structInstField
           (Term.structInstLVal `map [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`X `Y `f]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app
                `Option.elim'
                [`none
                 (Term.fun
                  "fun"
                  (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
               ","
               `rfl]
              "⟩"))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_id' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`X]
             []
             "=>"
             («term_<|_»
              (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
              "<|"
              (Term.app
               `funext
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`o]
                  []
                  "=>"
                  (Term.app
                   (Term.app `Option.recOn [`o `rfl])
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.app `Part.some_to_option [(Term.hole "_")])))])))])))))
          []
          (Term.structInstField
           (Term.structInstLVal `map_comp' [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`X `Y `Z `f `g]
             []
             "=>"
             («term_<|_»
              (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
              "<|"
              (Term.app
               `funext
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`o]
                  []
                  "=>"
                  (Term.app
                   (Term.app `Option.recOn [`o `rfl])
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))])))))]
         (Term.optEllipsis [])
         []
         "}")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.structInst
        "{"
        []
        [(Term.structInstField
          (Term.structInstLVal `obj [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`X]
            []
            "=>"
            (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩"))))
         []
         (Term.structInstField
          (Term.structInstLVal `map [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`X `Y `f]
            []
            "=>"
            (Term.anonymousCtor
             "⟨"
             [(Term.app
               `Option.elim'
               [`none
                (Term.fun
                 "fun"
                 (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
              ","
              `rfl]
             "⟩"))))
         []
         (Term.structInstField
          (Term.structInstLVal `map_id' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`X]
            []
            "=>"
            («term_<|_»
             (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
             "<|"
             (Term.app
              `funext
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`o]
                 []
                 "=>"
                 (Term.app
                  (Term.app `Option.recOn [`o `rfl])
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.app `Part.some_to_option [(Term.hole "_")])))])))])))))
         []
         (Term.structInstField
          (Term.structInstLVal `map_comp' [])
          ":="
          (Term.fun
           "fun"
           (Term.basicFun
            [`X `Y `Z `f `g]
            []
            "=>"
            («term_<|_»
             (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
             "<|"
             (Term.app
              `funext
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`o]
                 []
                 "=>"
                 (Term.app
                  (Term.app `Option.recOn [`o `rfl])
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))])))))]
        (Term.optEllipsis [])
        []
        "}"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `obj [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `map [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X `Y `f]
           []
           "=>"
           (Term.anonymousCtor
            "⟨"
            [(Term.app
              `Option.elim'
              [`none
               (Term.fun
                "fun"
                (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
             ","
             `rfl]
            "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_id' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           («term_<|_»
            (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
            "<|"
            (Term.app
             `funext
             [(Term.fun
               "fun"
               (Term.basicFun
                [`o]
                []
                "=>"
                (Term.app
                 (Term.app `Option.recOn [`o `rfl])
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.app `Part.some_to_option [(Term.hole "_")])))])))])))))
        []
        (Term.structInstField
         (Term.structInstLVal `map_comp' [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`X `Y `Z `f `g]
           []
           "=>"
           («term_<|_»
            (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
            "<|"
            (Term.app
             `funext
             [(Term.fun
               "fun"
               (Term.basicFun
                [`o]
                []
                "=>"
                (Term.app
                 (Term.app `Option.recOn [`o `rfl])
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))])))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y `Z `f `g]
        []
        "=>"
        («term_<|_»
         (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
         "<|"
         (Term.app
          `funext
          [(Term.fun
            "fun"
            (Term.basicFun
             [`o]
             []
             "=>"
             (Term.app
              (Term.app `Option.recOn [`o `rfl])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
       "<|"
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`o]
           []
           "=>"
           (Term.app
            (Term.app `Option.recOn [`o `rfl])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`o]
          []
          "=>"
          (Term.app
           (Term.app `Option.recOn [`o `rfl])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`a]
              []
              "=>"
              (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`o]
        []
        "=>"
        (Term.app
         (Term.app `Option.recOn [`o `rfl])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a]
            []
            "=>"
            (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Option.recOn [`o `rfl])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Part.bind_to_option [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Part.bind_to_option
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Option.recOn [`o `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Option.recOn [`o `rfl]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PointedCat.Hom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `g
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Z
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        («term_<|_»
         (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
         "<|"
         (Term.app
          `funext
          [(Term.fun
            "fun"
            (Term.basicFun
             [`o]
             []
             "=>"
             (Term.app
              (Term.app `Option.recOn [`o `rfl])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.app `Part.some_to_option [(Term.hole "_")])))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
       "<|"
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`o]
           []
           "=>"
           (Term.app
            (Term.app `Option.recOn [`o `rfl])
            [(Term.fun
              "fun"
              (Term.basicFun [`a] [] "=>" (Term.app `Part.some_to_option [(Term.hole "_")])))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`o]
          []
          "=>"
          (Term.app
           (Term.app `Option.recOn [`o `rfl])
           [(Term.fun
             "fun"
             (Term.basicFun [`a] [] "=>" (Term.app `Part.some_to_option [(Term.hole "_")])))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`o]
        []
        "=>"
        (Term.app
         (Term.app `Option.recOn [`o `rfl])
         [(Term.fun
           "fun"
           (Term.basicFun [`a] [] "=>" (Term.app `Part.some_to_option [(Term.hole "_")])))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Option.recOn [`o `rfl])
       [(Term.fun
         "fun"
         (Term.basicFun [`a] [] "=>" (Term.app `Part.some_to_option [(Term.hole "_")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`a] [] "=>" (Term.app `Part.some_to_option [(Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Part.some_to_option [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Part.some_to_option
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Option.recOn [`o `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `Option.recOn [`o `rfl]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `o
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PointedCat.Hom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y `f]
        []
        "=>"
        (Term.anonymousCtor
         "⟨"
         [(Term.app
           `Option.elim'
           [`none
            (Term.fun
             "fun"
             (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
          ","
          `rfl]
         "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor
       "⟨"
       [(Term.app
         `Option.elim'
         [`none
          (Term.fun
           "fun"
           (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
        ","
        `rfl]
       "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Option.elim'
       [`none
        (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun "fun" (Term.basicFun [`a] [] "=>" (Term.proj (Term.app `f [`a]) "." `toOption)))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `f [`a]) "." `toOption)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `f [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `f [`a]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      `none
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.elim'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `Option [`X]) "," `none] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Option [`X])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The functor which maps undefined values to a new point. This makes the maps total and creates
      pointed types. This the noncomputable part of the equivalence `PartialFun_equiv_Pointed`. It can't
      be computable because `= option.none` is decidable while the domain of a general `part` isn't. -/
    @[ simps map ]
    noncomputable
  def
    partialFunToPointed
    : PartialFunCat ⥤ PointedCat
    :=
      by
        skip
          <;>
          exact
            {
              obj := fun X => ⟨ Option X , none ⟩
                map := fun X Y f => ⟨ Option.elim' none fun a => f a . toOption , rfl ⟩
                map_id'
                  :=
                  fun
                    X
                      =>
                      PointedCat.Hom.ext _ _
                        <|
                        funext fun o => Option.recOn o rfl fun a => Part.some_to_option _
                map_comp'
                  :=
                  fun
                    X Y Z f g
                      =>
                      PointedCat.Hom.ext _ _
                        <|
                        funext fun o => Option.recOn o rfl fun a => Part.bind_to_option _ _
              }
#align PartialFun_to_Pointed partialFunToPointed

/- failed to parenthesize: parenthesize: uncaught backtrack exception
[PrettyPrinter.parenthesize.input] (Command.declaration
     (Command.declModifiers
      [(Command.docComment
        "/--"
        "The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.\n`part.equiv_option` made functorial. -/")]
      [(Term.attributes
        "@["
        [(Term.attrInstance (Term.attrKind []) (Attr.simps "simps" [] (Attr.simpsArgsRest [] [])))]
        "]")]
      []
      [(Command.noncomputable "noncomputable")]
      []
      [])
     (Command.def
      "def"
      (Command.declId `partialFunEquivPointed [])
      (Command.optDeclSig
       []
       [(Term.typeSpec
         ":"
         (CategoryTheory.CategoryTheory.Equivalence.«term_≌_»
          (Term.explicitUniv `PartialFunCat ".{" [`u] "}")
          " ≌ "
          `PointedCat))])
      (Command.declValSimple
       ":="
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.«tactic_<;>_»
            (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
            "<;>"
            (Tactic.exact
             "exact"
             (Term.app
              `equivalence.mk
              [`partialFunToPointed
               `pointedToPartialFun
               (Term.app
                (Term.app
                 `nat_iso.of_components
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`X]
                    []
                    "=>"
                    (Term.app
                     `PartialFunCat.Iso.mk
                     [(Term.structInst
                       "{"
                       []
                       [(Term.structInstField
                         (Term.structInstLVal `toFun [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.anonymousCtor
                            "⟨"
                            [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                            "⟩"))))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `invFun [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           («term_<|_»
                            `get
                            "<|"
                            (Term.app
                             (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                             [(Term.proj `a "." (fieldIdx "2"))])))))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `left_inv [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `right_inv [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.simp
                                "simp"
                                []
                                []
                                ["only"]
                                ["["
                                 [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                  ","
                                  (Tactic.simpLemma [] [] `some_get)
                                  ","
                                  (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                 "]"]
                                [])]))))))]
                       (Term.optEllipsis [])
                       []
                       "}")])))])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`X `Y `f]
                   []
                   "=>"
                   (Term.app
                    `Pfun.ext
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`a `b]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.unfoldProjs "unfold_projs" [] [])
                           []
                           (Tactic.dsimp "dsimp" [] [] [] [] [])
                           []
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                            [])
                           []
                           (Tactic.refine'
                            "refine'"
                            (Term.app
                             (Term.proj
                              (Term.app `part.mem_bind_iff.trans [(Term.hole "_")])
                              "."
                              `trans)
                             [`pfun.mem_to_subtype_iff.symm]))
                           []
                           (Std.Tactic.obtain
                            "obtain"
                            [(Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.tuple
                                "⟨"
                                [(Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `b)
                                    "|"
                                    (Std.Tactic.RCases.rcasesPat.one `b)])
                                  [])
                                 ","
                                 (Std.Tactic.RCases.rcasesPatLo
                                  (Std.Tactic.RCases.rcasesPatMed
                                   [(Std.Tactic.RCases.rcasesPat.one `hb)])
                                  [])]
                                "⟩")])]
                            []
                            [":=" [`b]])
                           []
                           (tactic___
                            (cdotTk (patternIgnore (token.«·» "·")))
                            [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                           []
                           (Tactic.dsimp "dsimp" [] [] [] [] [])
                           []
                           (Mathlib.Tactic.tacticSimp_rw__
                            "simp_rw"
                            (Tactic.rwRuleSeq
                             "["
                             [(Tactic.rwRule [] `Part.mem_some_iff)
                              ","
                              (Tactic.rwRule [] `Subtype.mk_eq_mk)
                              ","
                              (Tactic.rwRule [] `exists_prop)
                              ","
                              (Tactic.rwRule [] `some_inj)
                              ","
                              (Tactic.rwRule [] `exists_eq_right')]
                             "]")
                            [])
                           []
                           (Tactic.refine'
                            "refine'"
                            (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                           []
                           (Tactic.exact "exact" `eq_comm)])))))])))])
               (Term.app
                (Term.app
                 `nat_iso.of_components
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`X]
                    []
                    "=>"
                    (Term.app
                     `PointedCat.Iso.mk
                     [(Term.structInst
                       "{"
                       []
                       [(Term.structInstField
                         (Term.structInstLVal `toFun [])
                         ":="
                         (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `invFun [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (termDepIfThenElse
                            "if"
                            (Lean.binderIdent `h)
                            ":"
                            («term_=_» `a "=" (Term.proj `X "." `point))
                            "then"
                            `none
                            "else"
                            (Term.app
                             `some
                             [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `left_inv [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.app
                            (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                            [(Term.fun
                              "fun"
                              (Term.basicFun
                               [`a]
                               []
                               "=>"
                               («term_<|_»
                                (Term.proj
                                 (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                                 "."
                                 `trans)
                                "<|"
                                (Term.byTactic
                                 "by"
                                 (Tactic.tacticSeq
                                  (Tactic.tacticSeq1Indented
                                   [(Tactic.simp
                                     "simp"
                                     []
                                     []
                                     ["only"]
                                     ["["
                                      [(Tactic.simpLemma [] [] `Option.elim')
                                       ","
                                       (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                       ","
                                       (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                      "]"]
                                     [])]))))))]))))
                        []
                        (Term.structInstField
                         (Term.structInstLVal `right_inv [])
                         ":="
                         (Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.change
                                "change"
                                («term_=_»
                                 (Term.app
                                  `Option.elim'
                                  [(Term.hole "_")
                                   (Term.hole "_")
                                   (Term.app
                                    `dite
                                    [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                                 "="
                                 (Term.hole "_"))
                                [])
                               []
                               (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                               []
                               (tactic___
                                (cdotTk (patternIgnore (token.«·» "·")))
                                [(Tactic.rwSeq
                                  "rw"
                                  []
                                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                                  [])
                                 []
                                 (Tactic.tacticRfl "rfl")])
                               []
                               (tactic___
                                (cdotTk (patternIgnore (token.«·» "·")))
                                [(Tactic.tacticRfl "rfl")])]))))))]
                       (Term.optEllipsis [])
                       []
                       "}")
                      `rfl])))])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`X `Y `f]
                   []
                   "=>"
                   («term_<|_»
                    (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                    "<|"
                    (Term.app
                     `funext
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`a]
                        []
                        "=>"
                        (Term.app
                         (Term.app `Option.recOn [`a `f.map_point.symm])
                         [(Term.fun
                           "fun"
                           (Term.basicFun
                            [`a]
                            []
                            "=>"
                            (Term.byTactic
                             "by"
                             (Tactic.tacticSeq
                              (Tactic.tacticSeq1Indented
                               [(Tactic.unfoldProjs "unfold_projs" [] [])
                                []
                                (Tactic.dsimp "dsimp" [] [] [] [] [])
                                []
                                (Tactic.change
                                 "change"
                                 («term_=_»
                                  (Term.app
                                   `Option.elim'
                                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                                  "="
                                  (Term.hole "_"))
                                 [])
                                []
                                (Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq
                                  "["
                                  [(Tactic.rwRule [] `Part.elim_to_option)]
                                  "]")
                                 [])
                                []
                                (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                                []
                                (tactic___
                                 (cdotTk (patternIgnore (token.«·» "·")))
                                 [(Tactic.tacticRfl "rfl")])
                                []
                                (tactic___
                                 (cdotTk (patternIgnore (token.«·» "·")))
                                 [(Tactic.exact
                                   "exact"
                                   (Term.app
                                    `Eq.symm
                                    [(Term.app `of_not_not [`h])]))])])))))])))]))))])])))])))
       [])
      []
      []
      []))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.abbrev'
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
            (Term.app
             `equivalence.mk
             [`partialFunToPointed
              `pointedToPartialFun
              (Term.app
               (Term.app
                `nat_iso.of_components
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`X]
                   []
                   "=>"
                   (Term.app
                    `PartialFunCat.Iso.mk
                    [(Term.structInst
                      "{"
                      []
                      [(Term.structInstField
                        (Term.structInstLVal `toFun [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.anonymousCtor
                           "⟨"
                           [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                           "⟩"))))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `invFun [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          («term_<|_»
                           `get
                           "<|"
                           (Term.app
                            (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                            [(Term.proj `a "." (fieldIdx "2"))])))))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `left_inv [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `right_inv [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.simp
                               "simp"
                               []
                               []
                               ["only"]
                               ["["
                                [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                 ","
                                 (Tactic.simpLemma [] [] `some_get)
                                 ","
                                 (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                "]"]
                               [])]))))))]
                      (Term.optEllipsis [])
                      []
                      "}")])))])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`X `Y `f]
                  []
                  "=>"
                  (Term.app
                   `Pfun.ext
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a `b]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.unfoldProjs "unfold_projs" [] [])
                          []
                          (Tactic.dsimp "dsimp" [] [] [] [] [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                           [])
                          []
                          (Tactic.refine'
                           "refine'"
                           (Term.app
                            (Term.proj
                             (Term.app `part.mem_bind_iff.trans [(Term.hole "_")])
                             "."
                             `trans)
                            [`pfun.mem_to_subtype_iff.symm]))
                          []
                          (Std.Tactic.obtain
                           "obtain"
                           [(Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.tuple
                               "⟨"
                               [(Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `b)
                                   "|"
                                   (Std.Tactic.RCases.rcasesPat.one `b)])
                                 [])
                                ","
                                (Std.Tactic.RCases.rcasesPatLo
                                 (Std.Tactic.RCases.rcasesPatMed
                                  [(Std.Tactic.RCases.rcasesPat.one `hb)])
                                 [])]
                               "⟩")])]
                           []
                           [":=" [`b]])
                          []
                          (tactic___
                           (cdotTk (patternIgnore (token.«·» "·")))
                           [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                          []
                          (Tactic.dsimp "dsimp" [] [] [] [] [])
                          []
                          (Mathlib.Tactic.tacticSimp_rw__
                           "simp_rw"
                           (Tactic.rwRuleSeq
                            "["
                            [(Tactic.rwRule [] `Part.mem_some_iff)
                             ","
                             (Tactic.rwRule [] `Subtype.mk_eq_mk)
                             ","
                             (Tactic.rwRule [] `exists_prop)
                             ","
                             (Tactic.rwRule [] `some_inj)
                             ","
                             (Tactic.rwRule [] `exists_eq_right')]
                            "]")
                           [])
                          []
                          (Tactic.refine'
                           "refine'"
                           (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                          []
                          (Tactic.exact "exact" `eq_comm)])))))])))])
              (Term.app
               (Term.app
                `nat_iso.of_components
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`X]
                   []
                   "=>"
                   (Term.app
                    `PointedCat.Iso.mk
                    [(Term.structInst
                      "{"
                      []
                      [(Term.structInstField
                        (Term.structInstLVal `toFun [])
                        ":="
                        (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `invFun [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (termDepIfThenElse
                           "if"
                           (Lean.binderIdent `h)
                           ":"
                           («term_=_» `a "=" (Term.proj `X "." `point))
                           "then"
                           `none
                           "else"
                           (Term.app
                            `some
                            [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `left_inv [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.app
                           (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                           [(Term.fun
                             "fun"
                             (Term.basicFun
                              [`a]
                              []
                              "=>"
                              («term_<|_»
                               (Term.proj
                                (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                                "."
                                `trans)
                               "<|"
                               (Term.byTactic
                                "by"
                                (Tactic.tacticSeq
                                 (Tactic.tacticSeq1Indented
                                  [(Tactic.simp
                                    "simp"
                                    []
                                    []
                                    ["only"]
                                    ["["
                                     [(Tactic.simpLemma [] [] `Option.elim')
                                      ","
                                      (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                      ","
                                      (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                     "]"]
                                    [])]))))))]))))
                       []
                       (Term.structInstField
                        (Term.structInstLVal `right_inv [])
                        ":="
                        (Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.change
                               "change"
                               («term_=_»
                                (Term.app
                                 `Option.elim'
                                 [(Term.hole "_")
                                  (Term.hole "_")
                                  (Term.app
                                   `dite
                                   [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                                "="
                                (Term.hole "_"))
                               [])
                              []
                              (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                              []
                              (tactic___
                               (cdotTk (patternIgnore (token.«·» "·")))
                               [(Tactic.rwSeq
                                 "rw"
                                 []
                                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                                 [])
                                []
                                (Tactic.tacticRfl "rfl")])
                              []
                              (tactic___
                               (cdotTk (patternIgnore (token.«·» "·")))
                               [(Tactic.tacticRfl "rfl")])]))))))]
                      (Term.optEllipsis [])
                      []
                      "}")
                     `rfl])))])
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`X `Y `f]
                  []
                  "=>"
                  («term_<|_»
                   (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
                   "<|"
                   (Term.app
                    `funext
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`a]
                       []
                       "=>"
                       (Term.app
                        (Term.app `Option.recOn [`a `f.map_point.symm])
                        [(Term.fun
                          "fun"
                          (Term.basicFun
                           [`a]
                           []
                           "=>"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.unfoldProjs "unfold_projs" [] [])
                               []
                               (Tactic.dsimp "dsimp" [] [] [] [] [])
                               []
                               (Tactic.change
                                "change"
                                («term_=_»
                                 (Term.app
                                  `Option.elim'
                                  [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                                 "="
                                 (Term.hole "_"))
                                [])
                               []
                               (Tactic.rwSeq
                                "rw"
                                []
                                (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                                [])
                               []
                               (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                               []
                               (tactic___
                                (cdotTk (patternIgnore (token.«·» "·")))
                                [(Tactic.tacticRfl "rfl")])
                               []
                               (tactic___
                                (cdotTk (patternIgnore (token.«·» "·")))
                                [(Tactic.exact
                                  "exact"
                                  (Term.app
                                   `Eq.symm
                                   [(Term.app `of_not_not [`h])]))])])))))])))]))))])])))])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.«tactic_<;>_»
       (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
       "<;>"
       (Tactic.exact
        "exact"
        (Term.app
         `equivalence.mk
         [`partialFunToPointed
          `pointedToPartialFun
          (Term.app
           (Term.app
            `nat_iso.of_components
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                `PartialFunCat.Iso.mk
                [(Term.structInst
                  "{"
                  []
                  [(Term.structInstField
                    (Term.structInstLVal `toFun [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.anonymousCtor
                       "⟨"
                       [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                       "⟩"))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `invFun [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      («term_<|_»
                       `get
                       "<|"
                       (Term.app
                        (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                        [(Term.proj `a "." (fieldIdx "2"))])))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `left_inv [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `right_inv [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                             ","
                             (Tactic.simpLemma [] [] `some_get)
                             ","
                             (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                            "]"]
                           [])]))))))]
                  (Term.optEllipsis [])
                  []
                  "}")])))])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`X `Y `f]
              []
              "=>"
              (Term.app
               `Pfun.ext
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`a `b]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.unfoldProjs "unfold_projs" [] [])
                      []
                      (Tactic.dsimp "dsimp" [] [] [] [] [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                       [])
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app
                        (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                        [`pfun.mem_to_subtype_iff.symm]))
                      []
                      (Std.Tactic.obtain
                       "obtain"
                       [(Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.tuple
                           "⟨"
                           [(Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `b)
                               "|"
                               (Std.Tactic.RCases.rcasesPat.one `b)])
                             [])
                            ","
                            (Std.Tactic.RCases.rcasesPatLo
                             (Std.Tactic.RCases.rcasesPatMed
                              [(Std.Tactic.RCases.rcasesPat.one `hb)])
                             [])]
                           "⟩")])]
                       []
                       [":=" [`b]])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                      []
                      (Tactic.dsimp "dsimp" [] [] [] [] [])
                      []
                      (Mathlib.Tactic.tacticSimp_rw__
                       "simp_rw"
                       (Tactic.rwRuleSeq
                        "["
                        [(Tactic.rwRule [] `Part.mem_some_iff)
                         ","
                         (Tactic.rwRule [] `Subtype.mk_eq_mk)
                         ","
                         (Tactic.rwRule [] `exists_prop)
                         ","
                         (Tactic.rwRule [] `some_inj)
                         ","
                         (Tactic.rwRule [] `exists_eq_right')]
                        "]")
                       [])
                      []
                      (Tactic.refine'
                       "refine'"
                       (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                      []
                      (Tactic.exact "exact" `eq_comm)])))))])))])
          (Term.app
           (Term.app
            `nat_iso.of_components
            [(Term.fun
              "fun"
              (Term.basicFun
               [`X]
               []
               "=>"
               (Term.app
                `PointedCat.Iso.mk
                [(Term.structInst
                  "{"
                  []
                  [(Term.structInstField
                    (Term.structInstLVal `toFun [])
                    ":="
                    (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `invFun [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (termDepIfThenElse
                       "if"
                       (Lean.binderIdent `h)
                       ":"
                       («term_=_» `a "=" (Term.proj `X "." `point))
                       "then"
                       `none
                       "else"
                       (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `left_inv [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.app
                       (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                       [(Term.fun
                         "fun"
                         (Term.basicFun
                          [`a]
                          []
                          "=>"
                          («term_<|_»
                           (Term.proj
                            (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                            "."
                            `trans)
                           "<|"
                           (Term.byTactic
                            "by"
                            (Tactic.tacticSeq
                             (Tactic.tacticSeq1Indented
                              [(Tactic.simp
                                "simp"
                                []
                                []
                                ["only"]
                                ["["
                                 [(Tactic.simpLemma [] [] `Option.elim')
                                  ","
                                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                  ","
                                  (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                 "]"]
                                [])]))))))]))))
                   []
                   (Term.structInstField
                    (Term.structInstLVal `right_inv [])
                    ":="
                    (Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.change
                           "change"
                           («term_=_»
                            (Term.app
                             `Option.elim'
                             [(Term.hole "_")
                              (Term.hole "_")
                              (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                            "="
                            (Term.hole "_"))
                           [])
                          []
                          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                          []
                          (tactic___
                           (cdotTk (patternIgnore (token.«·» "·")))
                           [(Tactic.rwSeq
                             "rw"
                             []
                             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                             [])
                            []
                            (Tactic.tacticRfl "rfl")])
                          []
                          (tactic___
                           (cdotTk (patternIgnore (token.«·» "·")))
                           [(Tactic.tacticRfl "rfl")])]))))))]
                  (Term.optEllipsis [])
                  []
                  "}")
                 `rfl])))])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`X `Y `f]
              []
              "=>"
              («term_<|_»
               (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
               "<|"
               (Term.app
                `funext
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   []
                   "=>"
                   (Term.app
                    (Term.app `Option.recOn [`a `f.map_point.symm])
                    [(Term.fun
                      "fun"
                      (Term.basicFun
                       [`a]
                       []
                       "=>"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.unfoldProjs "unfold_projs" [] [])
                           []
                           (Tactic.dsimp "dsimp" [] [] [] [] [])
                           []
                           (Tactic.change
                            "change"
                            («term_=_»
                             (Term.app
                              `Option.elim'
                              [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                             "="
                             (Term.hole "_"))
                            [])
                           []
                           (Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                            [])
                           []
                           (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                           []
                           (tactic___
                            (cdotTk (patternIgnore (token.«·» "·")))
                            [(Tactic.tacticRfl "rfl")])
                           []
                           (tactic___
                            (cdotTk (patternIgnore (token.«·» "·")))
                            [(Tactic.exact
                              "exact"
                              (Term.app
                               `Eq.symm
                               [(Term.app `of_not_not [`h])]))])])))))])))]))))])])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact
       "exact"
       (Term.app
        `equivalence.mk
        [`partialFunToPointed
         `pointedToPartialFun
         (Term.app
          (Term.app
           `nat_iso.of_components
           [(Term.fun
             "fun"
             (Term.basicFun
              [`X]
              []
              "=>"
              (Term.app
               `PartialFunCat.Iso.mk
               [(Term.structInst
                 "{"
                 []
                 [(Term.structInstField
                   (Term.structInstLVal `toFun [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.anonymousCtor
                      "⟨"
                      [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                      "⟩"))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `invFun [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     («term_<|_»
                      `get
                      "<|"
                      (Term.app
                       (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                       [(Term.proj `a "." (fieldIdx "2"))])))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `left_inv [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `right_inv [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                            ","
                            (Tactic.simpLemma [] [] `some_get)
                            ","
                            (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                           "]"]
                          [])]))))))]
                 (Term.optEllipsis [])
                 []
                 "}")])))])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`X `Y `f]
             []
             "=>"
             (Term.app
              `Pfun.ext
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a `b]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.unfoldProjs "unfold_projs" [] [])
                     []
                     (Tactic.dsimp "dsimp" [] [] [] [] [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                      [])
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app
                       (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                       [`pfun.mem_to_subtype_iff.symm]))
                     []
                     (Std.Tactic.obtain
                      "obtain"
                      [(Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.tuple
                          "⟨"
                          [(Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed
                             [(Std.Tactic.RCases.rcasesPat.one `b)
                              "|"
                              (Std.Tactic.RCases.rcasesPat.one `b)])
                            [])
                           ","
                           (Std.Tactic.RCases.rcasesPatLo
                            (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                            [])]
                          "⟩")])]
                      []
                      [":=" [`b]])
                     []
                     (tactic___
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                     []
                     (Tactic.dsimp "dsimp" [] [] [] [] [])
                     []
                     (Mathlib.Tactic.tacticSimp_rw__
                      "simp_rw"
                      (Tactic.rwRuleSeq
                       "["
                       [(Tactic.rwRule [] `Part.mem_some_iff)
                        ","
                        (Tactic.rwRule [] `Subtype.mk_eq_mk)
                        ","
                        (Tactic.rwRule [] `exists_prop)
                        ","
                        (Tactic.rwRule [] `some_inj)
                        ","
                        (Tactic.rwRule [] `exists_eq_right')]
                       "]")
                      [])
                     []
                     (Tactic.refine'
                      "refine'"
                      (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                     []
                     (Tactic.exact "exact" `eq_comm)])))))])))])
         (Term.app
          (Term.app
           `nat_iso.of_components
           [(Term.fun
             "fun"
             (Term.basicFun
              [`X]
              []
              "=>"
              (Term.app
               `PointedCat.Iso.mk
               [(Term.structInst
                 "{"
                 []
                 [(Term.structInstField
                   (Term.structInstLVal `toFun [])
                   ":="
                   (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `invFun [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (termDepIfThenElse
                      "if"
                      (Lean.binderIdent `h)
                      ":"
                      («term_=_» `a "=" (Term.proj `X "." `point))
                      "then"
                      `none
                      "else"
                      (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `left_inv [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.app
                      (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                      [(Term.fun
                        "fun"
                        (Term.basicFun
                         [`a]
                         []
                         "=>"
                         («term_<|_»
                          (Term.proj
                           (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                           "."
                           `trans)
                          "<|"
                          (Term.byTactic
                           "by"
                           (Tactic.tacticSeq
                            (Tactic.tacticSeq1Indented
                             [(Tactic.simp
                               "simp"
                               []
                               []
                               ["only"]
                               ["["
                                [(Tactic.simpLemma [] [] `Option.elim')
                                 ","
                                 (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                 ","
                                 (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                                "]"]
                               [])]))))))]))))
                  []
                  (Term.structInstField
                   (Term.structInstLVal `right_inv [])
                   ":="
                   (Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.change
                          "change"
                          («term_=_»
                           (Term.app
                            `Option.elim'
                            [(Term.hole "_")
                             (Term.hole "_")
                             (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                           "="
                           (Term.hole "_"))
                          [])
                         []
                         (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                         []
                         (tactic___
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(Tactic.rwSeq
                            "rw"
                            []
                            (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                            [])
                           []
                           (Tactic.tacticRfl "rfl")])
                         []
                         (tactic___
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(Tactic.tacticRfl "rfl")])]))))))]
                 (Term.optEllipsis [])
                 []
                 "}")
                `rfl])))])
          [(Term.fun
            "fun"
            (Term.basicFun
             [`X `Y `f]
             []
             "=>"
             («term_<|_»
              (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
              "<|"
              (Term.app
               `funext
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.app
                   (Term.app `Option.recOn [`a `f.map_point.symm])
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.unfoldProjs "unfold_projs" [] [])
                          []
                          (Tactic.dsimp "dsimp" [] [] [] [] [])
                          []
                          (Tactic.change
                           "change"
                           («term_=_»
                            (Term.app
                             `Option.elim'
                             [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                            "="
                            (Term.hole "_"))
                           [])
                          []
                          (Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                           [])
                          []
                          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                          []
                          (tactic___
                           (cdotTk (patternIgnore (token.«·» "·")))
                           [(Tactic.tacticRfl "rfl")])
                          []
                          (tactic___
                           (cdotTk (patternIgnore (token.«·» "·")))
                           [(Tactic.exact
                             "exact"
                             (Term.app
                              `Eq.symm
                              [(Term.app `of_not_not [`h])]))])])))))])))]))))])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `equivalence.mk
       [`partialFunToPointed
        `pointedToPartialFun
        (Term.app
         (Term.app
          `nat_iso.of_components
          [(Term.fun
            "fun"
            (Term.basicFun
             [`X]
             []
             "=>"
             (Term.app
              `PartialFunCat.Iso.mk
              [(Term.structInst
                "{"
                []
                [(Term.structInstField
                  (Term.structInstLVal `toFun [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.anonymousCtor
                     "⟨"
                     [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                     "⟩"))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `invFun [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    («term_<|_»
                     `get
                     "<|"
                     (Term.app
                      (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                      [(Term.proj `a "." (fieldIdx "2"))])))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `left_inv [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `right_inv [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                           ","
                           (Tactic.simpLemma [] [] `some_get)
                           ","
                           (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                          "]"]
                         [])]))))))]
                (Term.optEllipsis [])
                []
                "}")])))])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`X `Y `f]
            []
            "=>"
            (Term.app
             `Pfun.ext
             [(Term.fun
               "fun"
               (Term.basicFun
                [`a `b]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.unfoldProjs "unfold_projs" [] [])
                    []
                    (Tactic.dsimp "dsimp" [] [] [] [] [])
                    []
                    (Tactic.rwSeq
                     "rw"
                     []
                     (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                     [])
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.app
                      (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                      [`pfun.mem_to_subtype_iff.symm]))
                    []
                    (Std.Tactic.obtain
                     "obtain"
                     [(Std.Tactic.RCases.rcasesPatMed
                       [(Std.Tactic.RCases.rcasesPat.tuple
                         "⟨"
                         [(Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed
                            [(Std.Tactic.RCases.rcasesPat.one `b)
                             "|"
                             (Std.Tactic.RCases.rcasesPat.one `b)])
                           [])
                          ","
                          (Std.Tactic.RCases.rcasesPatLo
                           (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                           [])]
                         "⟩")])]
                     []
                     [":=" [`b]])
                    []
                    (tactic___
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                    []
                    (Tactic.dsimp "dsimp" [] [] [] [] [])
                    []
                    (Mathlib.Tactic.tacticSimp_rw__
                     "simp_rw"
                     (Tactic.rwRuleSeq
                      "["
                      [(Tactic.rwRule [] `Part.mem_some_iff)
                       ","
                       (Tactic.rwRule [] `Subtype.mk_eq_mk)
                       ","
                       (Tactic.rwRule [] `exists_prop)
                       ","
                       (Tactic.rwRule [] `some_inj)
                       ","
                       (Tactic.rwRule [] `exists_eq_right')]
                      "]")
                     [])
                    []
                    (Tactic.refine'
                     "refine'"
                     (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                    []
                    (Tactic.exact "exact" `eq_comm)])))))])))])
        (Term.app
         (Term.app
          `nat_iso.of_components
          [(Term.fun
            "fun"
            (Term.basicFun
             [`X]
             []
             "=>"
             (Term.app
              `PointedCat.Iso.mk
              [(Term.structInst
                "{"
                []
                [(Term.structInstField
                  (Term.structInstLVal `toFun [])
                  ":="
                  (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `invFun [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (termDepIfThenElse
                     "if"
                     (Lean.binderIdent `h)
                     ":"
                     («term_=_» `a "=" (Term.proj `X "." `point))
                     "then"
                     `none
                     "else"
                     (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `left_inv [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.app
                     (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                     [(Term.fun
                       "fun"
                       (Term.basicFun
                        [`a]
                        []
                        "=>"
                        («term_<|_»
                         (Term.proj
                          (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                          "."
                          `trans)
                         "<|"
                         (Term.byTactic
                          "by"
                          (Tactic.tacticSeq
                           (Tactic.tacticSeq1Indented
                            [(Tactic.simp
                              "simp"
                              []
                              []
                              ["only"]
                              ["["
                               [(Tactic.simpLemma [] [] `Option.elim')
                                ","
                                (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                                ","
                                (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                               "]"]
                              [])]))))))]))))
                 []
                 (Term.structInstField
                  (Term.structInstLVal `right_inv [])
                  ":="
                  (Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.change
                         "change"
                         («term_=_»
                          (Term.app
                           `Option.elim'
                           [(Term.hole "_")
                            (Term.hole "_")
                            (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                          "="
                          (Term.hole "_"))
                         [])
                        []
                        (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                        []
                        (tactic___
                         (cdotTk (patternIgnore (token.«·» "·")))
                         [(Tactic.rwSeq
                           "rw"
                           []
                           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]")
                           [])
                          []
                          (Tactic.tacticRfl "rfl")])
                        []
                        (tactic___
                         (cdotTk (patternIgnore (token.«·» "·")))
                         [(Tactic.tacticRfl "rfl")])]))))))]
                (Term.optEllipsis [])
                []
                "}")
               `rfl])))])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`X `Y `f]
            []
            "=>"
            («term_<|_»
             (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
             "<|"
             (Term.app
              `funext
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.app
                  (Term.app `Option.recOn [`a `f.map_point.symm])
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.unfoldProjs "unfold_projs" [] [])
                         []
                         (Tactic.dsimp "dsimp" [] [] [] [] [])
                         []
                         (Tactic.change
                          "change"
                          («term_=_»
                           (Term.app
                            `Option.elim'
                            [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                           "="
                           (Term.hole "_"))
                          [])
                         []
                         (Tactic.rwSeq
                          "rw"
                          []
                          (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                          [])
                         []
                         (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                         []
                         (tactic___
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(Tactic.tacticRfl "rfl")])
                         []
                         (tactic___
                          (cdotTk (patternIgnore (token.«·» "·")))
                          [(Tactic.exact
                            "exact"
                            (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))]))))])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app
        `nat_iso.of_components
        [(Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (Term.app
            `PointedCat.Iso.mk
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
               []
               (Term.structInstField
                (Term.structInstLVal `invFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h)
                   ":"
                   («term_=_» `a "=" (Term.proj `X "." `point))
                   "then"
                   `none
                   "else"
                   (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
               []
               (Term.structInstField
                (Term.structInstLVal `left_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.app
                   (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      («term_<|_»
                       (Term.proj
                        (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
                        "."
                        `trans)
                       "<|"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `Option.elim')
                              ","
                              (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                              ","
                              (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                             "]"]
                            [])]))))))]))))
               []
               (Term.structInstField
                (Term.structInstLVal `right_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.change
                       "change"
                       («term_=_»
                        (Term.app
                         `Option.elim'
                         [(Term.hole "_")
                          (Term.hole "_")
                          (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                        "="
                        (Term.hole "_"))
                       [])
                      []
                      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                        []
                        (Tactic.tacticRfl "rfl")])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.tacticRfl "rfl")])]))))))]
              (Term.optEllipsis [])
              []
              "}")
             `rfl])))])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X `Y `f]
          []
          "=>"
          («term_<|_»
           (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
           "<|"
           (Term.app
            `funext
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.app
                (Term.app `Option.recOn [`a `f.map_point.symm])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   []
                   "=>"
                   (Term.byTactic
                    "by"
                    (Tactic.tacticSeq
                     (Tactic.tacticSeq1Indented
                      [(Tactic.unfoldProjs "unfold_projs" [] [])
                       []
                       (Tactic.dsimp "dsimp" [] [] [] [] [])
                       []
                       (Tactic.change
                        "change"
                        («term_=_»
                         (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         "="
                         (Term.hole "_"))
                        [])
                       []
                       (Tactic.rwSeq
                        "rw"
                        []
                        (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                        [])
                       []
                       (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                       []
                       (tactic___
                        (cdotTk (patternIgnore (token.«·» "·")))
                        [(Tactic.tacticRfl "rfl")])
                       []
                       (tactic___
                        (cdotTk (patternIgnore (token.«·» "·")))
                        [(Tactic.exact
                          "exact"
                          (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))]))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y `f]
        []
        "=>"
        («term_<|_»
         (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
         "<|"
         (Term.app
          `funext
          [(Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.app
              (Term.app `Option.recOn [`a `f.map_point.symm])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.unfoldProjs "unfold_projs" [] [])
                     []
                     (Tactic.dsimp "dsimp" [] [] [] [] [])
                     []
                     (Tactic.change
                      "change"
                      («term_=_»
                       (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                       "="
                       (Term.hole "_"))
                      [])
                     []
                     (Tactic.rwSeq
                      "rw"
                      []
                      (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                      [])
                     []
                     (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
                     []
                     (tactic___
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(Tactic.exact
                        "exact"
                        (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
       "<|"
       (Term.app
        `funext
        [(Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.app
            (Term.app `Option.recOn [`a `f.map_point.symm])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.unfoldProjs "unfold_projs" [] [])
                   []
                   (Tactic.dsimp "dsimp" [] [] [] [] [])
                   []
                   (Tactic.change
                    "change"
                    («term_=_»
                     (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                     "="
                     (Term.hole "_"))
                    [])
                   []
                   (Tactic.rwSeq
                    "rw"
                    []
                    (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                    [])
                   []
                   (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                   []
                   (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
                   []
                   (tactic___
                    (cdotTk (patternIgnore (token.«·» "·")))
                    [(Tactic.exact
                      "exact"
                      (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `funext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.app
           (Term.app `Option.recOn [`a `f.map_point.symm])
           [(Term.fun
             "fun"
             (Term.basicFun
              [`a]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.unfoldProjs "unfold_projs" [] [])
                  []
                  (Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Tactic.change
                   "change"
                   («term_=_»
                    (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                    "="
                    (Term.hole "_"))
                   [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                   [])
                  []
                  (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                  []
                  (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
                  []
                  (tactic___
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(Tactic.exact
                     "exact"
                     (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app
         (Term.app `Option.recOn [`a `f.map_point.symm])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.unfoldProjs "unfold_projs" [] [])
                []
                (Tactic.dsimp "dsimp" [] [] [] [] [])
                []
                (Tactic.change
                 "change"
                 («term_=_»
                  (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                  "="
                  (Term.hole "_"))
                 [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                 [])
                []
                (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                []
                (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
                []
                (tactic___
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(Tactic.exact
                   "exact"
                   (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Option.recOn [`a `f.map_point.symm])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.unfoldProjs "unfold_projs" [] [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.change
               "change"
               («term_=_»
                (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                "="
                (Term.hole "_"))
               [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
               [])
              []
              (Mathlib.Tactic.splitIfs "split_ifs" [] [])
              []
              (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
              []
              (tactic___
               (cdotTk (patternIgnore (token.«·» "·")))
               [(Tactic.exact "exact" (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.unfoldProjs "unfold_projs" [] [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.change
             "change"
             («term_=_»
              (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
              "="
              (Term.hole "_"))
             [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
             [])
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
            []
            (tactic___
             (cdotTk (patternIgnore (token.«·» "·")))
             [(Tactic.exact "exact" (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.unfoldProjs "unfold_projs" [] [])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.change
           "change"
           («term_=_»
            (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
            "="
            (Term.hole "_"))
           [])
          []
          (Tactic.rwSeq
           "rw"
           []
           (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
           [])
          []
          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
          []
          (tactic___
           (cdotTk (patternIgnore (token.«·» "·")))
           [(Tactic.exact "exact" (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic___
       (cdotTk (patternIgnore (token.«·» "·")))
       [(Tactic.exact "exact" (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.app `Eq.symm [(Term.app `of_not_not [`h])]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Eq.symm [(Term.app `of_not_not [`h])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `of_not_not [`h])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `of_not_not
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `of_not_not [`h]) ")")
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Eq.symm
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Part.elim_to_option
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
       "="
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `Option.elim'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfoldProjs "unfold_projs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Option.recOn [`a `f.map_point.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f.map_point.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Option.recOn [`a `f.map_point.symm])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `funext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PointedCat.Hom.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `nat_iso.of_components
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X]
          []
          "=>"
          (Term.app
           `PointedCat.Iso.mk
           [(Term.structInst
             "{"
             []
             [(Term.structInstField
               (Term.structInstLVal `toFun [])
               ":="
               (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
              []
              (Term.structInstField
               (Term.structInstLVal `invFun [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (termDepIfThenElse
                  "if"
                  (Lean.binderIdent `h)
                  ":"
                  («term_=_» `a "=" (Term.proj `X "." `point))
                  "then"
                  `none
                  "else"
                  (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
              []
              (Term.structInstField
               (Term.structInstLVal `left_inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.app
                  (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                  [(Term.fun
                    "fun"
                    (Term.basicFun
                     [`a]
                     []
                     "=>"
                     («term_<|_»
                      (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
                      "<|"
                      (Term.byTactic
                       "by"
                       (Tactic.tacticSeq
                        (Tactic.tacticSeq1Indented
                         [(Tactic.simp
                           "simp"
                           []
                           []
                           ["only"]
                           ["["
                            [(Tactic.simpLemma [] [] `Option.elim')
                             ","
                             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                             ","
                             (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                            "]"]
                           [])]))))))]))))
              []
              (Term.structInstField
               (Term.structInstLVal `right_inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.change
                      "change"
                      («term_=_»
                       (Term.app
                        `Option.elim'
                        [(Term.hole "_")
                         (Term.hole "_")
                         (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                       "="
                       (Term.hole "_"))
                      [])
                     []
                     (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                     []
                     (tactic___
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                       []
                       (Tactic.tacticRfl "rfl")])
                     []
                     (tactic___
                      (cdotTk (patternIgnore (token.«·» "·")))
                      [(Tactic.tacticRfl "rfl")])]))))))]
             (Term.optEllipsis [])
             []
             "}")
            `rfl])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        (Term.app
         `PointedCat.Iso.mk
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
            []
            (Term.structInstField
             (Term.structInstLVal `invFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (termDepIfThenElse
                "if"
                (Lean.binderIdent `h)
                ":"
                («term_=_» `a "=" (Term.proj `X "." `point))
                "then"
                `none
                "else"
                (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
            []
            (Term.structInstField
             (Term.structInstLVal `left_inv [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.app
                (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
                [(Term.fun
                  "fun"
                  (Term.basicFun
                   [`a]
                   []
                   "=>"
                   («term_<|_»
                    (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
                    "<|"
                    (Term.byTactic
                     "by"
                     (Tactic.tacticSeq
                      (Tactic.tacticSeq1Indented
                       [(Tactic.simp
                         "simp"
                         []
                         []
                         ["only"]
                         ["["
                          [(Tactic.simpLemma [] [] `Option.elim')
                           ","
                           (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                           ","
                           (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                          "]"]
                         [])]))))))]))))
            []
            (Term.structInstField
             (Term.structInstLVal `right_inv [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.change
                    "change"
                    («term_=_»
                     (Term.app
                      `Option.elim'
                      [(Term.hole "_")
                       (Term.hole "_")
                       (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                     "="
                     (Term.hole "_"))
                    [])
                   []
                   (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                   []
                   (tactic___
                    (cdotTk (patternIgnore (token.«·» "·")))
                    [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                     []
                     (Tactic.tacticRfl "rfl")])
                   []
                   (tactic___
                    (cdotTk (patternIgnore (token.«·» "·")))
                    [(Tactic.tacticRfl "rfl")])]))))))]
           (Term.optEllipsis [])
           []
           "}")
          `rfl])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `PointedCat.Iso.mk
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
          []
          (Term.structInstField
           (Term.structInstLVal `invFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (termDepIfThenElse
              "if"
              (Lean.binderIdent `h)
              ":"
              («term_=_» `a "=" (Term.proj `X "." `point))
              "then"
              `none
              "else"
              (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
          []
          (Term.structInstField
           (Term.structInstLVal `left_inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.app
              (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
              [(Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 («term_<|_»
                  (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
                  "<|"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `Option.elim')
                         ","
                         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                         ","
                         (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                        "]"]
                       [])]))))))]))))
          []
          (Term.structInstField
           (Term.structInstLVal `right_inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.change
                  "change"
                  («term_=_»
                   (Term.app
                    `Option.elim'
                    [(Term.hole "_")
                     (Term.hole "_")
                     (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                   "="
                   (Term.hole "_"))
                  [])
                 []
                 (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                 []
                 (tactic___
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                   []
                   (Tactic.tacticRfl "rfl")])
                 []
                 (tactic___
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(Tactic.tacticRfl "rfl")])]))))))]
         (Term.optEllipsis [])
         []
         "}")
        `rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
        []
        (Term.structInstField
         (Term.structInstLVal `invFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (termDepIfThenElse
            "if"
            (Lean.binderIdent `h)
            ":"
            («term_=_» `a "=" (Term.proj `X "." `point))
            "then"
            `none
            "else"
            (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
        []
        (Term.structInstField
         (Term.structInstLVal `left_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.app
            (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
            [(Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               («term_<|_»
                (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
                "<|"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Option.elim')
                       ","
                       (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                      "]"]
                     [])]))))))]))))
        []
        (Term.structInstField
         (Term.structInstLVal `right_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.change
                "change"
                («term_=_»
                 (Term.app
                  `Option.elim'
                  [(Term.hole "_")
                   (Term.hole "_")
                   (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
                 "="
                 (Term.hole "_"))
                [])
               []
               (Mathlib.Tactic.splitIfs "split_ifs" [] [])
               []
               (tactic___
                (cdotTk (patternIgnore (token.«·» "·")))
                [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                 []
                 (Tactic.tacticRfl "rfl")])
               []
               (tactic___
                (cdotTk (patternIgnore (token.«·» "·")))
                [(Tactic.tacticRfl "rfl")])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.change
             "change"
             («term_=_»
              (Term.app
               `Option.elim'
               [(Term.hole "_")
                (Term.hole "_")
                (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
              "="
              (Term.hole "_"))
             [])
            []
            (Mathlib.Tactic.splitIfs "split_ifs" [] [])
            []
            (tactic___
             (cdotTk (patternIgnore (token.«·» "·")))
             [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
              []
              (Tactic.tacticRfl "rfl")])
            []
            (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.change
           "change"
           («term_=_»
            (Term.app
             `Option.elim'
             [(Term.hole "_")
              (Term.hole "_")
              (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
            "="
            (Term.hole "_"))
           [])
          []
          (Mathlib.Tactic.splitIfs "split_ifs" [] [])
          []
          (tactic___
           (cdotTk (patternIgnore (token.«·» "·")))
           [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
            []
            (Tactic.tacticRfl "rfl")])
          []
          (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic___ (cdotTk (patternIgnore (token.«·» "·"))) [(Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic___
       (cdotTk (patternIgnore (token.«·» "·")))
       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
        []
        (Tactic.tacticRfl "rfl")])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.tacticRfl "rfl")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.change
       "change"
       («term_=_»
        (Term.app
         `Option.elim'
         [(Term.hole "_")
          (Term.hole "_")
          (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
        "="
        (Term.hole "_"))
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_»
       (Term.app
        `Option.elim'
        [(Term.hole "_")
         (Term.hole "_")
         (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
       "="
       (Term.hole "_"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      (Term.app
       `Option.elim'
       [(Term.hole "_")
        (Term.hole "_")
        (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
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
      `dite
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1023, term))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1023, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.elim'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1022, (some 1023, term) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.app
         (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a]
            []
            "=>"
            («term_<|_»
             (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
             "<|"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Option.elim')
                    ","
                    (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                    ","
                    (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                   "]"]
                  [])]))))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a]
          []
          "=>"
          («term_<|_»
           (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
           "<|"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Option.elim')
                  ","
                  (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                 "]"]
                [])]))))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        («term_<|_»
         (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
         "<|"
         (Term.byTactic
          "by"
          (Tactic.tacticSeq
           (Tactic.tacticSeq1Indented
            [(Tactic.simp
              "simp"
              []
              []
              ["only"]
              ["["
               [(Tactic.simpLemma [] [] `Option.elim')
                ","
                (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                ","
                (Tactic.simpLemma [] [] `Subtype.coe_eta)]
               "]"]
              [])]))))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
       "<|"
       (Term.byTactic
        "by"
        (Tactic.tacticSeq
         (Tactic.tacticSeq1Indented
          [(Tactic.simp
            "simp"
            []
            []
            ["only"]
            ["["
             [(Tactic.simpLemma [] [] `Option.elim')
              ","
              (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
              ","
              (Tactic.simpLemma [] [] `Subtype.coe_eta)]
             "]"]
            [])]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Option.elim')
             ","
             (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_eta)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Option.elim')
         ","
         (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_eta)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_eta
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Option.elim'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      (Term.proj (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `a "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dif_neg
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app `Option.recOn [`a (Term.app `dif_pos [`rfl])])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `dif_pos [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `dif_pos
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `dif_pos [`rfl]) ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.recOn
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 1023,
     term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `Option.recOn [`a (Term.paren "(" (Term.app `dif_pos [`rfl]) ")")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (termDepIfThenElse
         "if"
         (Lean.binderIdent `h)
         ":"
         («term_=_» `a "=" (Term.proj `X "." `point))
         "then"
         `none
         "else"
         (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (termDepIfThenElse
       "if"
       (Lean.binderIdent `h)
       ":"
       («term_=_» `a "=" (Term.proj `X "." `point))
       "then"
       `none
       "else"
       (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.anonymousCtor', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `h
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `none
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_=_» `a "=" (Term.proj `X "." `point))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `X "." `point)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 50, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 51 >? 1024, (none, [anonymous]) <=? (some 50, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 50, (some 51, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.proj `X "." `point)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Option.elim'
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PointedCat.Iso.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nat_iso.of_components
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `nat_iso.of_components
      [(Term.fun
        "fun"
        (Term.basicFun
         [`X]
         []
         "=>"
         (Term.app
          `PointedCat.Iso.mk
          [(Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `toFun [])
              ":="
              (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
             []
             (Term.structInstField
              (Term.structInstLVal `invFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                (termDepIfThenElse
                 "if"
                 (Lean.binderIdent `h)
                 ":"
                 («term_=_» `a "=" (Term.proj `X "." `point))
                 "then"
                 `none
                 "else"
                 (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
             []
             (Term.structInstField
              (Term.structInstLVal `left_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                (Term.app
                 (Term.paren
                  "("
                  (Term.app `Option.recOn [`a (Term.paren "(" (Term.app `dif_pos [`rfl]) ")")])
                  ")")
                 [(Term.fun
                   "fun"
                   (Term.basicFun
                    [`a]
                    []
                    "=>"
                    («term_<|_»
                     (Term.proj
                      (Term.paren "(" (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) ")")
                      "."
                      `trans)
                     "<|"
                     (Term.byTactic
                      "by"
                      (Tactic.tacticSeq
                       (Tactic.tacticSeq1Indented
                        [(Tactic.simp
                          "simp"
                          []
                          []
                          ["only"]
                          ["["
                           [(Tactic.simpLemma [] [] `Option.elim')
                            ","
                            (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                            ","
                            (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                           "]"]
                          [])]))))))]))))
             []
             (Term.structInstField
              (Term.structInstLVal `right_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.change
                     "change"
                     («term_=_»
                      (Term.app
                       `Option.elim'
                       [(Term.hole "_")
                        (Term.hole "_")
                        (Term.paren
                         "("
                         (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                         ")")])
                      "="
                      (Term.hole "_"))
                     [])
                    []
                    (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                    []
                    (tactic___
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                      []
                      (Tactic.tacticRfl "rfl")])
                    []
                    (tactic___
                     (cdotTk (patternIgnore (token.«·» "·")))
                     [(Tactic.tacticRfl "rfl")])]))))))]
            (Term.optEllipsis [])
            []
            "}")
           `rfl])))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren
       "("
       (Term.app
        `nat_iso.of_components
        [(Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (Term.app
            `PointedCat.Iso.mk
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.app `Option.elim' [(Term.proj `X "." `point) `Subtype.val]))
               []
               (Term.structInstField
                (Term.structInstLVal `invFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (termDepIfThenElse
                   "if"
                   (Lean.binderIdent `h)
                   ":"
                   («term_=_» `a "=" (Term.proj `X "." `point))
                   "then"
                   `none
                   "else"
                   (Term.app `some [(Term.anonymousCtor "⟨" [(Term.hole "_") "," `h] "⟩")])))))
               []
               (Term.structInstField
                (Term.structInstLVal `left_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.app
                   (Term.paren
                    "("
                    (Term.app `Option.recOn [`a (Term.paren "(" (Term.app `dif_pos [`rfl]) ")")])
                    ")")
                   [(Term.fun
                     "fun"
                     (Term.basicFun
                      [`a]
                      []
                      "=>"
                      («term_<|_»
                       (Term.proj
                        (Term.paren "(" (Term.app `dif_neg [(Term.proj `a "." (fieldIdx "2"))]) ")")
                        "."
                        `trans)
                       "<|"
                       (Term.byTactic
                        "by"
                        (Tactic.tacticSeq
                         (Tactic.tacticSeq1Indented
                          [(Tactic.simp
                            "simp"
                            []
                            []
                            ["only"]
                            ["["
                             [(Tactic.simpLemma [] [] `Option.elim')
                              ","
                              (Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                              ","
                              (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                             "]"]
                            [])]))))))]))))
               []
               (Term.structInstField
                (Term.structInstLVal `right_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.change
                       "change"
                       («term_=_»
                        (Term.app
                         `Option.elim'
                         [(Term.hole "_")
                          (Term.hole "_")
                          (Term.paren
                           "("
                           (Term.app `dite [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                           ")")])
                        "="
                        (Term.hole "_"))
                       [])
                      []
                      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `h)] "]") [])
                        []
                        (Tactic.tacticRfl "rfl")])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.tacticRfl "rfl")])]))))))]
              (Term.optEllipsis [])
              []
              "}")
             `rfl])))])
       ")")
      [(Term.fun
        "fun"
        (Term.basicFun
         [`X `Y `f]
         []
         "=>"
         («term_<|_»
          (Term.app `PointedCat.Hom.ext [(Term.hole "_") (Term.hole "_")])
          "<|"
          (Term.app
           `funext
           [(Term.fun
             "fun"
             (Term.basicFun
              [`a]
              []
              "=>"
              (Term.app
               (Term.paren "(" (Term.app `Option.recOn [`a `f.map_point.symm]) ")")
               [(Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.unfoldProjs "unfold_projs" [] [])
                      []
                      (Tactic.dsimp "dsimp" [] [] [] [] [])
                      []
                      (Tactic.change
                       "change"
                       («term_=_»
                        (Term.app `Option.elim' [(Term.hole "_") (Term.hole "_") (Term.hole "_")])
                        "="
                        (Term.hole "_"))
                       [])
                      []
                      (Tactic.rwSeq
                       "rw"
                       []
                       (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.elim_to_option)] "]")
                       [])
                      []
                      (Mathlib.Tactic.splitIfs "split_ifs" [] [])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.tacticRfl "rfl")])
                      []
                      (tactic___
                       (cdotTk (patternIgnore (token.«·» "·")))
                       [(Tactic.exact
                         "exact"
                         (Term.app
                          `Eq.symm
                          [(Term.paren "(" (Term.app `of_not_not [`h]) ")")]))])])))))])))]))))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.app', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app
       (Term.app
        `nat_iso.of_components
        [(Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (Term.app
            `PartialFunCat.Iso.mk
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                   "⟩"))))
               []
               (Term.structInstField
                (Term.structInstLVal `invFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  («term_<|_»
                   `get
                   "<|"
                   (Term.app
                    (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                    [(Term.proj `a "." (fieldIdx "2"))])))))
               []
               (Term.structInstField
                (Term.structInstLVal `left_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
               []
               (Term.structInstField
                (Term.structInstLVal `right_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                         ","
                         (Tactic.simpLemma [] [] `some_get)
                         ","
                         (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                        "]"]
                       [])]))))))]
              (Term.optEllipsis [])
              []
              "}")])))])
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X `Y `f]
          []
          "=>"
          (Term.app
           `Pfun.ext
           [(Term.fun
             "fun"
             (Term.basicFun
              [`a `b]
              []
              "=>"
              (Term.byTactic
               "by"
               (Tactic.tacticSeq
                (Tactic.tacticSeq1Indented
                 [(Tactic.unfoldProjs "unfold_projs" [] [])
                  []
                  (Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Tactic.rwSeq
                   "rw"
                   []
                   (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app
                    (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                    [`pfun.mem_to_subtype_iff.symm]))
                  []
                  (Std.Tactic.obtain
                   "obtain"
                   [(Std.Tactic.RCases.rcasesPatMed
                     [(Std.Tactic.RCases.rcasesPat.tuple
                       "⟨"
                       [(Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed
                          [(Std.Tactic.RCases.rcasesPat.one `b)
                           "|"
                           (Std.Tactic.RCases.rcasesPat.one `b)])
                         [])
                        ","
                        (Std.Tactic.RCases.rcasesPatLo
                         (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                         [])]
                       "⟩")])]
                   []
                   [":=" [`b]])
                  []
                  (tactic___
                   (cdotTk (patternIgnore (token.«·» "·")))
                   [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                  []
                  (Tactic.dsimp "dsimp" [] [] [] [] [])
                  []
                  (Mathlib.Tactic.tacticSimp_rw__
                   "simp_rw"
                   (Tactic.rwRuleSeq
                    "["
                    [(Tactic.rwRule [] `Part.mem_some_iff)
                     ","
                     (Tactic.rwRule [] `Subtype.mk_eq_mk)
                     ","
                     (Tactic.rwRule [] `exists_prop)
                     ","
                     (Tactic.rwRule [] `some_inj)
                     ","
                     (Tactic.rwRule [] `exists_eq_right')]
                    "]")
                   [])
                  []
                  (Tactic.refine'
                   "refine'"
                   (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                  []
                  (Tactic.exact "exact" `eq_comm)])))))])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X `Y `f]
        []
        "=>"
        (Term.app
         `Pfun.ext
         [(Term.fun
           "fun"
           (Term.basicFun
            [`a `b]
            []
            "=>"
            (Term.byTactic
             "by"
             (Tactic.tacticSeq
              (Tactic.tacticSeq1Indented
               [(Tactic.unfoldProjs "unfold_projs" [] [])
                []
                (Tactic.dsimp "dsimp" [] [] [] [] [])
                []
                (Tactic.rwSeq
                 "rw"
                 []
                 (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app
                  (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                  [`pfun.mem_to_subtype_iff.symm]))
                []
                (Std.Tactic.obtain
                 "obtain"
                 [(Std.Tactic.RCases.rcasesPatMed
                   [(Std.Tactic.RCases.rcasesPat.tuple
                     "⟨"
                     [(Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed
                        [(Std.Tactic.RCases.rcasesPat.one `b)
                         "|"
                         (Std.Tactic.RCases.rcasesPat.one `b)])
                       [])
                      ","
                      (Std.Tactic.RCases.rcasesPatLo
                       (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                       [])]
                     "⟩")])]
                 []
                 [":=" [`b]])
                []
                (tactic___
                 (cdotTk (patternIgnore (token.«·» "·")))
                 [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
                []
                (Tactic.dsimp "dsimp" [] [] [] [] [])
                []
                (Mathlib.Tactic.tacticSimp_rw__
                 "simp_rw"
                 (Tactic.rwRuleSeq
                  "["
                  [(Tactic.rwRule [] `Part.mem_some_iff)
                   ","
                   (Tactic.rwRule [] `Subtype.mk_eq_mk)
                   ","
                   (Tactic.rwRule [] `exists_prop)
                   ","
                   (Tactic.rwRule [] `some_inj)
                   ","
                   (Tactic.rwRule [] `exists_eq_right')]
                  "]")
                 [])
                []
                (Tactic.refine'
                 "refine'"
                 (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                []
                (Tactic.exact "exact" `eq_comm)])))))])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `Pfun.ext
       [(Term.fun
         "fun"
         (Term.basicFun
          [`a `b]
          []
          "=>"
          (Term.byTactic
           "by"
           (Tactic.tacticSeq
            (Tactic.tacticSeq1Indented
             [(Tactic.unfoldProjs "unfold_projs" [] [])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Tactic.rwSeq
               "rw"
               []
               (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
               [])
              []
              (Tactic.refine'
               "refine'"
               (Term.app
                (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
                [`pfun.mem_to_subtype_iff.symm]))
              []
              (Std.Tactic.obtain
               "obtain"
               [(Std.Tactic.RCases.rcasesPatMed
                 [(Std.Tactic.RCases.rcasesPat.tuple
                   "⟨"
                   [(Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed
                      [(Std.Tactic.RCases.rcasesPat.one `b)
                       "|"
                       (Std.Tactic.RCases.rcasesPat.one `b)])
                     [])
                    ","
                    (Std.Tactic.RCases.rcasesPatLo
                     (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                     [])]
                   "⟩")])]
               []
               [":=" [`b]])
              []
              (tactic___
               (cdotTk (patternIgnore (token.«·» "·")))
               [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
              []
              (Tactic.dsimp "dsimp" [] [] [] [] [])
              []
              (Mathlib.Tactic.tacticSimp_rw__
               "simp_rw"
               (Tactic.rwRuleSeq
                "["
                [(Tactic.rwRule [] `Part.mem_some_iff)
                 ","
                 (Tactic.rwRule [] `Subtype.mk_eq_mk)
                 ","
                 (Tactic.rwRule [] `exists_prop)
                 ","
                 (Tactic.rwRule [] `some_inj)
                 ","
                 (Tactic.rwRule [] `exists_eq_right')]
                "]")
               [])
              []
              (Tactic.refine' "refine'" (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
              []
              (Tactic.exact "exact" `eq_comm)])))))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a `b]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.unfoldProjs "unfold_projs" [] [])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Tactic.rwSeq
             "rw"
             []
             (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
             [])
            []
            (Tactic.refine'
             "refine'"
             (Term.app
              (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
              [`pfun.mem_to_subtype_iff.symm]))
            []
            (Std.Tactic.obtain
             "obtain"
             [(Std.Tactic.RCases.rcasesPatMed
               [(Std.Tactic.RCases.rcasesPat.tuple
                 "⟨"
                 [(Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.one `b) "|" (Std.Tactic.RCases.rcasesPat.one `b)])
                   [])
                  ","
                  (Std.Tactic.RCases.rcasesPatLo
                   (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                   [])]
                 "⟩")])]
             []
             [":=" [`b]])
            []
            (tactic___
             (cdotTk (patternIgnore (token.«·» "·")))
             [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
            []
            (Tactic.dsimp "dsimp" [] [] [] [] [])
            []
            (Mathlib.Tactic.tacticSimp_rw__
             "simp_rw"
             (Tactic.rwRuleSeq
              "["
              [(Tactic.rwRule [] `Part.mem_some_iff)
               ","
               (Tactic.rwRule [] `Subtype.mk_eq_mk)
               ","
               (Tactic.rwRule [] `exists_prop)
               ","
               (Tactic.rwRule [] `some_inj)
               ","
               (Tactic.rwRule [] `exists_eq_right')]
              "]")
             [])
            []
            (Tactic.refine' "refine'" (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
            []
            (Tactic.exact "exact" `eq_comm)])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.unfoldProjs "unfold_projs" [] [])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]") [])
          []
          (Tactic.refine'
           "refine'"
           (Term.app
            (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
            [`pfun.mem_to_subtype_iff.symm]))
          []
          (Std.Tactic.obtain
           "obtain"
           [(Std.Tactic.RCases.rcasesPatMed
             [(Std.Tactic.RCases.rcasesPat.tuple
               "⟨"
               [(Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed
                  [(Std.Tactic.RCases.rcasesPat.one `b) "|" (Std.Tactic.RCases.rcasesPat.one `b)])
                 [])
                ","
                (Std.Tactic.RCases.rcasesPatLo
                 (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                 [])]
               "⟩")])]
           []
           [":=" [`b]])
          []
          (tactic___
           (cdotTk (patternIgnore (token.«·» "·")))
           [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
          []
          (Tactic.dsimp "dsimp" [] [] [] [] [])
          []
          (Mathlib.Tactic.tacticSimp_rw__
           "simp_rw"
           (Tactic.rwRuleSeq
            "["
            [(Tactic.rwRule [] `Part.mem_some_iff)
             ","
             (Tactic.rwRule [] `Subtype.mk_eq_mk)
             ","
             (Tactic.rwRule [] `exists_prop)
             ","
             (Tactic.rwRule [] `some_inj)
             ","
             (Tactic.rwRule [] `exists_eq_right')]
            "]")
           [])
          []
          (Tactic.refine' "refine'" (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
          []
          (Tactic.exact "exact" `eq_comm)])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" `eq_comm)
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `eq_comm
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine' "refine'" (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `part.mem_to_option.symm.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Mathlib.Tactic.tacticSimp_rw__
       "simp_rw"
       (Tactic.rwRuleSeq
        "["
        [(Tactic.rwRule [] `Part.mem_some_iff)
         ","
         (Tactic.rwRule [] `Subtype.mk_eq_mk)
         ","
         (Tactic.rwRule [] `exists_prop)
         ","
         (Tactic.rwRule [] `some_inj)
         ","
         (Tactic.rwRule [] `exists_eq_right')]
        "]")
       [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_eq_right'
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `some_inj
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `exists_prop
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.mk_eq_mk
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Part.mem_some_iff
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (tactic___
       (cdotTk (patternIgnore (token.«·» "·")))
       [(Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.exact "exact" (Term.proj (Term.app `hb [`rfl]) "." `elim))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj (Term.app `hb [`rfl]) "." `elim)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `hb [`rfl])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `rfl
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `hb
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren "(" (Term.app `hb [`rfl]) ")")
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Std.Tactic.obtain
       "obtain"
       [(Std.Tactic.RCases.rcasesPatMed
         [(Std.Tactic.RCases.rcasesPat.tuple
           "⟨"
           [(Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed
              [(Std.Tactic.RCases.rcasesPat.one `b) "|" (Std.Tactic.RCases.rcasesPat.one `b)])
             [])
            ","
            (Std.Tactic.RCases.rcasesPatLo
             (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
             [])]
           "⟩")])]
       []
       [":=" [`b]])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.refine'
       "refine'"
       (Term.app
        (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
        [`pfun.mem_to_subtype_iff.symm]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
       [`pfun.mem_to_subtype_iff.symm])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `pfun.mem_to_subtype_iff.symm
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) "." `trans)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      (Term.app `part.mem_bind_iff.trans [(Term.hole "_")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.hole', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.hole "_")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `part.mem_bind_iff.trans
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app `part.mem_bind_iff.trans [(Term.hole "_")])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.rwSeq "rw" [] (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]") [])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Part.bind_some
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.dsimp "dsimp" [] [] [] [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.unfoldProjs "unfold_projs" [] [])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `b
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `Pfun.ext
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `f
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `Y
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.app
       `nat_iso.of_components
       [(Term.fun
         "fun"
         (Term.basicFun
          [`X]
          []
          "=>"
          (Term.app
           `PartialFunCat.Iso.mk
           [(Term.structInst
             "{"
             []
             [(Term.structInstField
               (Term.structInstLVal `toFun [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.anonymousCtor
                  "⟨"
                  [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                  "⟩"))))
              []
              (Term.structInstField
               (Term.structInstLVal `invFun [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 («term_<|_»
                  `get
                  "<|"
                  (Term.app
                   (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                   [(Term.proj `a "." (fieldIdx "2"))])))))
              []
              (Term.structInstField
               (Term.structInstLVal `left_inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
              []
              (Term.structInstField
               (Term.structInstLVal `right_inv [])
               ":="
               (Term.fun
                "fun"
                (Term.basicFun
                 [`a]
                 []
                 "=>"
                 (Term.byTactic
                  "by"
                  (Tactic.tacticSeq
                   (Tactic.tacticSeq1Indented
                    [(Tactic.simp
                      "simp"
                      []
                      []
                      ["only"]
                      ["["
                       [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                        ","
                        (Tactic.simpLemma [] [] `some_get)
                        ","
                        (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                       "]"]
                      [])]))))))]
             (Term.optEllipsis [])
             []
             "}")])))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.fun', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`X]
        []
        "=>"
        (Term.app
         `PartialFunCat.Iso.mk
         [(Term.structInst
           "{"
           []
           [(Term.structInstField
             (Term.structInstLVal `toFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.anonymousCtor
                "⟨"
                [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                "⟩"))))
            []
            (Term.structInstField
             (Term.structInstLVal `invFun [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               («term_<|_»
                `get
                "<|"
                (Term.app
                 (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                 [(Term.proj `a "." (fieldIdx "2"))])))))
            []
            (Term.structInstField
             (Term.structInstLVal `left_inv [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun [`a] [] "=>" (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
            []
            (Term.structInstField
             (Term.structInstLVal `right_inv [])
             ":="
             (Term.fun
              "fun"
              (Term.basicFun
               [`a]
               []
               "=>"
               (Term.byTactic
                "by"
                (Tactic.tacticSeq
                 (Tactic.tacticSeq1Indented
                  [(Tactic.simp
                    "simp"
                    []
                    []
                    ["only"]
                    ["["
                     [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                      ","
                      (Tactic.simpLemma [] [] `some_get)
                      ","
                      (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                     "]"]
                    [])]))))))]
           (Term.optEllipsis [])
           []
           "}")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       `PartialFunCat.Iso.mk
       [(Term.structInst
         "{"
         []
         [(Term.structInstField
           (Term.structInstLVal `toFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.anonymousCtor
              "⟨"
              [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
              "⟩"))))
          []
          (Term.structInstField
           (Term.structInstLVal `invFun [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             («term_<|_»
              `get
              "<|"
              (Term.app
               (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
               [(Term.proj `a "." (fieldIdx "2"))])))))
          []
          (Term.structInstField
           (Term.structInstLVal `left_inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun [`a] [] "=>" (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
          []
          (Term.structInstField
           (Term.structInstLVal `right_inv [])
           ":="
           (Term.fun
            "fun"
            (Term.basicFun
             [`a]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.simp
                  "simp"
                  []
                  []
                  ["only"]
                  ["["
                   [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                    ","
                    (Tactic.simpLemma [] [] `some_get)
                    ","
                    (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                   "]"]
                  [])]))))))]
         (Term.optEllipsis [])
         []
         "}")])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInst', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.structInst
       "{"
       []
       [(Term.structInstField
         (Term.structInstLVal `toFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.anonymousCtor "⟨" [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])] "⟩"))))
        []
        (Term.structInstField
         (Term.structInstLVal `invFun [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           («term_<|_»
            `get
            "<|"
            (Term.app
             (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
             [(Term.proj `a "." (fieldIdx "2"))])))))
        []
        (Term.structInstField
         (Term.structInstLVal `left_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun [`a] [] "=>" (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
        []
        (Term.structInstField
         (Term.structInstLVal `right_inv [])
         ":="
         (Term.fun
          "fun"
          (Term.basicFun
           [`a]
           []
           "=>"
           (Term.byTactic
            "by"
            (Tactic.tacticSeq
             (Tactic.tacticSeq1Indented
              [(Tactic.simp
                "simp"
                []
                []
                ["only"]
                ["["
                 [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                  ","
                  (Tactic.simpLemma [] [] `some_get)
                  ","
                  (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                 "]"]
                [])]))))))]
       (Term.optEllipsis [])
       []
       "}")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.byTactic
         "by"
         (Tactic.tacticSeq
          (Tactic.tacticSeq1Indented
           [(Tactic.simp
             "simp"
             []
             []
             ["only"]
             ["["
              [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
               ","
               (Tactic.simpLemma [] [] `some_get)
               ","
               (Tactic.simpLemma [] [] `Subtype.coe_eta)]
              "]"]
             [])])))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.byTactic
       "by"
       (Tactic.tacticSeq
        (Tactic.tacticSeq1Indented
         [(Tactic.simp
           "simp"
           []
           []
           ["only"]
           ["["
            [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
             ","
             (Tactic.simpLemma [] [] `some_get)
             ","
             (Tactic.simpLemma [] [] `Subtype.coe_eta)]
            "]"]
           [])])))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.tacticSeq1Indented', expected 'Lean.Parser.Tactic.tacticSeqBracketed'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Tactic.simp
       "simp"
       []
       []
       ["only"]
       ["["
        [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
         ","
         (Tactic.simpLemma [] [] `some_get)
         ","
         (Tactic.simpLemma [] [] `Subtype.coe_eta)]
        "]"]
       [])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.coe_eta
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `some_get
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpStar'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.simpLemma', expected 'Lean.Parser.Tactic.simpErase'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `Subtype.val_eq_coe
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 0, tactic) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun [`a] [] "=>" (Term.app `get_some [(Term.hole "_") (Term.hole "_")])))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `get_some [(Term.hole "_") (Term.hole "_")])
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
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `get_some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        («term_<|_»
         `get
         "<|"
         (Term.app
          (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
          [(Term.proj `a "." (fieldIdx "2"))]))))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      («term_<|_»
       `get
       "<|"
       (Term.app
        (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
        [(Term.proj `a "." (fieldIdx "2"))]))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app
       (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
       [(Term.proj `a "." (fieldIdx "2"))])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.proj', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.proj `a "." (fieldIdx "2"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `a
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `ne_none_iff_is_some
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 10 >? 1022, (some 1023,
     term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 10, term))
      `get
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none, [anonymous]) <=? (some 10, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 10, (some 10, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Term.structInstField', expected 'Lean.Parser.Term.structInstFieldAbbrev'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.fun
       "fun"
       (Term.basicFun
        [`a]
        []
        "=>"
        (Term.anonymousCtor "⟨" [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])] "⟩")))
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.anonymousCtor "⟨" [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])] "⟩")
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some_ne_none [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some_ne_none
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      (Term.app `some [`a])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `some
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `a
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `PartialFunCat.Iso.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.strictImplicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.implicitBinder'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.instBinder'
[PrettyPrinter.parenthesize] parenthesizing (cont := (none, [anonymous]))
      `X
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (some 0, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `nat_iso.of_components
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1022, (some 0, term) <=? (some 1022, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      `nat_iso.of_components
      [(Term.fun
        "fun"
        (Term.basicFun
         [`X]
         []
         "=>"
         (Term.app
          `PartialFunCat.Iso.mk
          [(Term.structInst
            "{"
            []
            [(Term.structInstField
              (Term.structInstLVal `toFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                (Term.anonymousCtor
                 "⟨"
                 [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                 "⟩"))))
             []
             (Term.structInstField
              (Term.structInstLVal `invFun [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                («term_<|_»
                 `get
                 "<|"
                 (Term.app
                  (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                  [(Term.proj `a "." (fieldIdx "2"))])))))
             []
             (Term.structInstField
              (Term.structInstLVal `left_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun [`a] [] "=>" (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
             []
             (Term.structInstField
              (Term.structInstLVal `right_inv [])
              ":="
              (Term.fun
               "fun"
               (Term.basicFun
                [`a]
                []
                "=>"
                (Term.byTactic
                 "by"
                 (Tactic.tacticSeq
                  (Tactic.tacticSeq1Indented
                   [(Tactic.simp
                     "simp"
                     []
                     []
                     ["only"]
                     ["["
                      [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                       ","
                       (Tactic.simpLemma [] [] `some_get)
                       ","
                       (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                      "]"]
                     [])]))))))]
            (Term.optEllipsis [])
            []
            "}")])))])
     ")")
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1022, (some 0, term) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesized: (Term.paren
     "("
     (Term.app
      (Term.paren
       "("
       (Term.app
        `nat_iso.of_components
        [(Term.fun
          "fun"
          (Term.basicFun
           [`X]
           []
           "=>"
           (Term.app
            `PartialFunCat.Iso.mk
            [(Term.structInst
              "{"
              []
              [(Term.structInstField
                (Term.structInstLVal `toFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.anonymousCtor
                   "⟨"
                   [(Term.app `some [`a]) "," (Term.app `some_ne_none [`a])]
                   "⟩"))))
               []
               (Term.structInstField
                (Term.structInstLVal `invFun [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  («term_<|_»
                   `get
                   "<|"
                   (Term.app
                    (Term.proj `ne_none_iff_is_some "." (fieldIdx "1"))
                    [(Term.proj `a "." (fieldIdx "2"))])))))
               []
               (Term.structInstField
                (Term.structInstLVal `left_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.app `get_some [(Term.hole "_") (Term.hole "_")]))))
               []
               (Term.structInstField
                (Term.structInstLVal `right_inv [])
                ":="
                (Term.fun
                 "fun"
                 (Term.basicFun
                  [`a]
                  []
                  "=>"
                  (Term.byTactic
                   "by"
                   (Tactic.tacticSeq
                    (Tactic.tacticSeq1Indented
                     [(Tactic.simp
                       "simp"
                       []
                       []
                       ["only"]
                       ["["
                        [(Tactic.simpLemma [] [] `Subtype.val_eq_coe)
                         ","
                         (Tactic.simpLemma [] [] `some_get)
                         ","
                         (Tactic.simpLemma [] [] `Subtype.coe_eta)]
                        "]"]
                       [])]))))))]
              (Term.optEllipsis [])
              []
              "}")])))])
       ")")
      [(Term.fun
        "fun"
        (Term.basicFun
         [`X `Y `f]
         []
         "=>"
         (Term.app
          `Pfun.ext
          [(Term.fun
            "fun"
            (Term.basicFun
             [`a `b]
             []
             "=>"
             (Term.byTactic
              "by"
              (Tactic.tacticSeq
               (Tactic.tacticSeq1Indented
                [(Tactic.unfoldProjs "unfold_projs" [] [])
                 []
                 (Tactic.dsimp "dsimp" [] [] [] [] [])
                 []
                 (Tactic.rwSeq
                  "rw"
                  []
                  (Tactic.rwRuleSeq "[" [(Tactic.rwRule [] `Part.bind_some)] "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app
                   (Term.proj
                    (Term.paren "(" (Term.app `part.mem_bind_iff.trans [(Term.hole "_")]) ")")
                    "."
                    `trans)
                   [`pfun.mem_to_subtype_iff.symm]))
                 []
                 (Std.Tactic.obtain
                  "obtain"
                  [(Std.Tactic.RCases.rcasesPatMed
                    [(Std.Tactic.RCases.rcasesPat.tuple
                      "⟨"
                      [(Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed
                         [(Std.Tactic.RCases.rcasesPat.one `b)
                          "|"
                          (Std.Tactic.RCases.rcasesPat.one `b)])
                        [])
                       ","
                       (Std.Tactic.RCases.rcasesPatLo
                        (Std.Tactic.RCases.rcasesPatMed [(Std.Tactic.RCases.rcasesPat.one `hb)])
                        [])]
                      "⟩")])]
                  []
                  [":=" [`b]])
                 []
                 (tactic___
                  (cdotTk (patternIgnore (token.«·» "·")))
                  [(Tactic.exact
                    "exact"
                    (Term.proj (Term.paren "(" (Term.app `hb [`rfl]) ")") "." `elim))])
                 []
                 (Tactic.dsimp "dsimp" [] [] [] [] [])
                 []
                 (Mathlib.Tactic.tacticSimp_rw__
                  "simp_rw"
                  (Tactic.rwRuleSeq
                   "["
                   [(Tactic.rwRule [] `Part.mem_some_iff)
                    ","
                    (Tactic.rwRule [] `Subtype.mk_eq_mk)
                    ","
                    (Tactic.rwRule [] `exists_prop)
                    ","
                    (Tactic.rwRule [] `some_inj)
                    ","
                    (Tactic.rwRule [] `exists_eq_right')]
                   "]")
                  [])
                 []
                 (Tactic.refine'
                  "refine'"
                  (Term.app `part.mem_to_option.symm.trans [(Term.hole "_")]))
                 []
                 (Tactic.exact "exact" `eq_comm)])))))])))])
     ")")
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `pointedToPartialFun
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.namedArgument'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'ident', expected 'Lean.Parser.Term.ellipsis'
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1024, term))
      `partialFunToPointed
[PrettyPrinter.parenthesize] ...precedences are 1023 >? 1024, (none,
     [anonymous]) <=? (some 1024, term)
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1022, term))
      `equivalence.mk
[PrettyPrinter.parenthesize] ...precedences are 1024 >? 1024, (none,
     [anonymous]) <=? (some 1022, term)
[PrettyPrinter.parenthesize] ...precedences are 0 >? 1022, (some 1023, term) <=? (none, [anonymous])
[PrettyPrinter.parenthesize] ...precedences are 2 >? 1022
[PrettyPrinter.parenthesize] parenthesizing (cont := (some 1, tactic))
      (Mathlib.Tactic.tacticClassical_ (Tactic.skip "skip"))
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Tactic.skip', expected 'Lean.Parser.Tactic.tacticSeq'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.declValEqns'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.declValSimple', expected 'Lean.Parser.Command.whereStructInst'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.theorem'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.opaque'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.instance'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.axiom'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.example'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.inductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.classInductive'
[PrettyPrinter.parenthesize.backtrack] unexpected node kind 'Lean.Parser.Command.def', expected 'Lean.Parser.Command.structure'-/-- failed to format: format: uncaught backtrack exception
/--
      The equivalence induced by `PartialFun_to_Pointed` and `Pointed_to_PartialFun`.
      `part.equiv_option` made functorial. -/
    @[ simps ]
    noncomputable
  def
    partialFunEquivPointed
    : PartialFunCat .{ u } ≌ PointedCat
    :=
      by
        skip
          <;>
          exact
            equivalence.mk
              partialFunToPointed
                pointedToPartialFun
                nat_iso.of_components
                    fun
                      X
                        =>
                        PartialFunCat.Iso.mk
                          {
                            toFun := fun a => ⟨ some a , some_ne_none a ⟩
                              invFun := fun a => get <| ne_none_iff_is_some . 1 a . 2
                              left_inv := fun a => get_some _ _
                              right_inv
                                :=
                                fun
                                  a
                                    =>
                                    by simp only [ Subtype.val_eq_coe , some_get , Subtype.coe_eta ]
                            }
                  fun
                    X Y f
                      =>
                      Pfun.ext
                        fun
                          a b
                            =>
                            by
                              unfold_projs
                                dsimp
                                rw [ Part.bind_some ]
                                refine'
                                  part.mem_bind_iff.trans _ . trans pfun.mem_to_subtype_iff.symm
                                obtain ⟨ b | b , hb ⟩ := b
                                · exact hb rfl . elim
                                dsimp
                                simp_rw
                                  [
                                    Part.mem_some_iff
                                      ,
                                      Subtype.mk_eq_mk
                                      ,
                                      exists_prop
                                      ,
                                      some_inj
                                      ,
                                      exists_eq_right'
                                    ]
                                refine' part.mem_to_option.symm.trans _
                                exact eq_comm
                nat_iso.of_components
                    fun
                      X
                        =>
                        PointedCat.Iso.mk
                          {
                              toFun := Option.elim' X . point Subtype.val
                                invFun
                                  :=
                                  fun a => if h : a = X . point then none else some ⟨ _ , h ⟩
                                left_inv
                                  :=
                                  fun
                                    a
                                      =>
                                      Option.recOn a dif_pos rfl
                                        fun
                                          a
                                            =>
                                            dif_neg a . 2 . trans
                                              <|
                                              by
                                                simp
                                                  only
                                                  [
                                                    Option.elim'
                                                      ,
                                                      Subtype.val_eq_coe
                                                      ,
                                                      Subtype.coe_eta
                                                    ]
                                right_inv
                                  :=
                                  fun
                                    a
                                      =>
                                      by
                                        change Option.elim' _ _ dite _ _ _ = _
                                          split_ifs
                                          · rw [ h ] rfl
                                          · rfl
                              }
                            rfl
                  fun
                    X Y f
                      =>
                      PointedCat.Hom.ext _ _
                        <|
                        funext
                          fun
                            a
                              =>
                              Option.recOn a f.map_point.symm
                                fun
                                  a
                                    =>
                                    by
                                      unfold_projs
                                        dsimp
                                        change Option.elim' _ _ _ = _
                                        rw [ Part.elim_to_option ]
                                        split_ifs
                                        · rfl
                                        · exact Eq.symm of_not_not h
#align PartialFun_equiv_Pointed partialFunEquivPointed

/-- Forgetting that maps are total and making them total again by adding a point is the same as just
adding a point. -/
@[simps]
noncomputable def typeToPartialFunIsoPartialFunToPointed :
    typeToPartialFun ⋙ partialFunToPointed ≅ typeToPointed :=
  (NatIso.ofComponents fun X =>
      { Hom := ⟨id, rfl⟩
        inv := ⟨id, rfl⟩
        hom_inv_id' := rfl
        inv_hom_id' := rfl })
    fun X Y f =>
    PointedCat.Hom.ext _ _ <|
      funext fun a => (Option.recOn a rfl) fun a => by convert Part.some_to_option _
#align Type_to_PartialFun_iso_PartialFun_to_Pointed typeToPartialFunIsoPartialFunToPointed

